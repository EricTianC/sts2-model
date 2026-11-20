#!/usr/bin/env python3
"""Export the pinned Windows x64 STS2 assembly with the official ILSpy CLI."""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request
import zipfile


ROOT = Path(__file__).resolve().parent.parent
CACHE = ROOT / ".agent_works" / "ilspy"
ILSPY_VERSION = "11.2.0.10050"
GUI_NAME = f"ILSpy_windows_selfcontained_{ILSPY_VERSION}-x64.zip"
GUI_URL = f"https://github.com/icsharpcode/ILSpy/releases/download/v11.2/{GUI_NAME}"
GUI_SHA256 = "c30cda0e5a22435df5013eeffa515594abf144e2d06c9bb5ddcc9fccdefd69c8"
CLI_NAME = f"ilspycmd.win-x64.{ILSPY_VERSION}.nupkg"
CLI_URL = f"https://api.nuget.org/v3-flatcontainer/ilspycmd.win-x64/{ILSPY_VERSION}/{CLI_NAME}"
CLI_SHA256 = "b67478eb22fedff149c37e7dd4512d716c5e1dbe7425a591ae8cf8eb773da158"
CLI_MEMBER = "tools/any/win-x64/ilspycmd.exe"

GAME_VERSION = "v0.113.1"
GAME_COMMIT = "d09d48e5"
GAME_DATA = "data_sts2_windows_x86_64"
ASSEMBLY_MVID = "9d417b39-1d40-4fc7-b993-28acdc29e151"
ASSEMBLY_FILES = {
    "sts2.dll": "62ecbe91093e1fa862de4329aac865209dcb297804caf0f0520d92d8c0b4a9c3",
    "sts2.xml": "3f6b673544929e27d51ce91bc467c427d2a6ade6a9dbd19f77019470ab828291",
}
PROJECT_FLAGS = ("--project", "--languageversion", "CSharp14_0")
SOURCE_COUNT = 3887
SOURCE_SHA256 = "7cbd0b6f14a4bdde406995337fab135d1703b948a9b76324889e695c269d440e"
DECOMPILER_DIAGNOSTIC = re.compile(rb"^[ \t]*//[ \t]*(?:IL_[0-9a-f]{4}:|Error decompiling\b)", re.I | re.M)


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def check_sha256(path, expected):
    actual = sha256(path)
    if actual != expected:
        raise ValueError(f"{path}: SHA-256 mismatch (expected {expected}, got {actual})")


def download_asset(name, url, expected):
    CACHE.mkdir(parents=True, exist_ok=True)
    cached = CACHE / name
    if cached.exists():
        check_sha256(cached, expected)
        return cached
    print(f"Downloading {url}", flush=True)
    with tempfile.TemporaryDirectory(prefix="download-", dir=CACHE) as working:
        partial = Path(working) / name
        with urllib.request.urlopen(url, timeout=60) as response, partial.open("wb") as dest:
            shutil.copyfileobj(response, dest)
        check_sha256(partial, expected)
        partial.rename(cached)
    return cached


def ilspy(exe, *args, capture=False):
    return subprocess.run(
        [exe, "--disable-updatecheck", *args],
        check=True, capture_output=capture, encoding="utf-8",
    ).stdout


def metadata_rows(exe, dll, table):
    return json.loads(ilspy(exe, "--dump-table", table, "--json", dll, capture=True))["rows"]


def check_game(game_dir):
    release = json.loads((game_dir / "release_info.json").read_text(encoding="utf-8-sig"))
    version, commit = release.get("version"), release.get("commit")
    if (version, commit) != (GAME_VERSION, GAME_COMMIT):
        raise ValueError(f"{game_dir}: expected {GAME_VERSION} ({GAME_COMMIT}), got {version} ({commit})")
    data = game_dir / GAME_DATA
    for name, expected in ASSEMBLY_FILES.items():
        check_sha256(data / name, expected)
    return data


def check_references(exe, data):
    dll = data / "sts2.dll"
    if [row["Mvid"] for row in metadata_rows(exe, dll, "Module")] != [ASSEMBLY_MVID]:
        raise ValueError(f"{dll}: unexpected MVID")
    references = sorted(row["Name"] + ".dll" for row in metadata_rows(exe, dll, "AssemblyRef"))
    missing = [name for name in references if not (data / name).is_file()]
    if missing:
        raise ValueError(f"{data}: missing assembly references: {', '.join(missing)}")
    # Keep the dependency fingerprints, not machine-specific resolver paths.
    return {name: sha256(data / name) for name in references}


def source_fingerprint(project):
    if not (project / "sts2.csproj").is_file():
        raise ValueError("ILSpy did not emit sts2.csproj")
    sources = sorted(project.rglob("*.cs"), key=lambda path: path.relative_to(project).as_posix())
    if len(sources) != SOURCE_COUNT:
        raise ValueError(f"expected {SOURCE_COUNT} C# files, got {len(sources)}")
    digest = hashlib.sha256()
    for path in sources:
        relative = path.relative_to(project).as_posix()
        content = path.read_bytes()
        if not content.strip() or DECOMPILER_DIAGNOSTIC.search(content):
            raise ValueError(f"ILSpy emitted an empty file or decompiler diagnostic: {relative}")
        digest.update(f"{relative}\0{hashlib.sha256(content).hexdigest()}\n".encode("utf-8"))
    return digest.hexdigest()


def decompile(game_dir, output_name):
    if sys.platform != "win32" or platform.machine().upper() not in {"AMD64", "X86_64"}:
        raise ValueError("the pinned automatic workflow requires Windows x64")
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]*", output_name):
        raise ValueError("--output-name must be a single directory name using letters, digits, hyphens or underscores")
    reference = ROOT / "reference"
    target = reference / output_name
    if target.exists() or target.is_symlink():
        raise ValueError(f"{target}: already exists; choose a fresh --output-name")
    data = check_game(game_dir.resolve())
    package = download_asset(CLI_NAME, CLI_URL, CLI_SHA256)
    reference.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="cli-", dir=CACHE) as tool_dir:
        exe = Path(tool_dir) / "ilspycmd.exe"
        with zipfile.ZipFile(package) as archive, archive.open(CLI_MEMBER) as src, exe.open("wb") as dest:
            shutil.copyfileobj(src, dest)
        version_lines = ilspy(exe, "--version", capture=True).splitlines()
        if version_lines != [f"ilspycmd: {ILSPY_VERSION}", f"ICSharpCode.Decompiler: {ILSPY_VERSION}"]:
            raise ValueError(f"unexpected ILSpy version output: {version_lines}")
        references = check_references(exe, data)
        # A sibling staging directory keeps generated project HintPaths valid after publication.
        with tempfile.TemporaryDirectory(prefix=".decompile-", dir=reference) as stage:
            project = Path(stage)
            ilspy(exe, *PROJECT_FLAGS, "--referencepath", data, "--outputdir", project, data / "sts2.dll")
            source_sha256 = source_fingerprint(project)
            if source_sha256 != SOURCE_SHA256:
                raise ValueError(f"unexpected C# tree SHA-256: expected {SOURCE_SHA256}, got {source_sha256}")
            manifest = {
                "schemaVersion": 1,
                "gameVersion": GAME_VERSION,
                "gameCommit": GAME_COMMIT,
                "assemblyMvid": ASSEMBLY_MVID,
                "gameFilesSha256": ASSEMBLY_FILES,
                "directReferencesSha256": references,
                "ilspyPackage": {"version": ILSPY_VERSION, "url": CLI_URL, "sha256": CLI_SHA256},
                "options": ["--disable-updatecheck", *PROJECT_FLAGS, "--referencepath", "<game-data>"],
                "sourceFiles": SOURCE_COUNT,
                "sourceSha256": source_sha256,
            }
            (project / "decompilation.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
            project.rename(target)
    print(f"{target}: {SOURCE_COUNT} C# files, {len(references)} local references, source SHA-256 {source_sha256}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("gui", help="cache the verified GitHub self-contained Windows x64 ZIP")
    export = commands.add_parser("decompile", help="export a fresh local C# reference tree")
    export.add_argument("game_dir", type=Path, help="Steam game directory containing release_info.json")
    export.add_argument("--output-name", default="sts2", help="new directory under reference/ (default: sts2)")
    args = parser.parse_args()
    try:
        if args.command == "gui":
            print(download_asset(GUI_NAME, GUI_URL, GUI_SHA256))
        else:
            decompile(args.game_dir, args.output_name)
    except (OSError, ValueError, KeyError, zipfile.BadZipFile, subprocess.CalledProcessError) as exc:
        if isinstance(exc, subprocess.CalledProcessError) and exc.stderr:
            print(exc.stderr, file=sys.stderr, end="")
        print(f"{parser.prog}: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
