using System.Reflection;

namespace HarmonyLib
{
    public class Harmony
    {
        public string Id { get; }

        public Harmony(string id)
        {
            Id = id;
        }

        public void PatchAll(Assembly assembly) { }

        public MethodInfo? Patch(
            MethodBase original,
            HarmonyMethod? prefix = null,
            HarmonyMethod? postfix = null,
            HarmonyMethod? transpiler = null,
            HarmonyMethod? finalizer = null) => null;
    }

    public class HarmonyMethod
    {
        public MethodInfo method;

        public HarmonyMethod(MethodInfo method)
        {
            this.method = method;
        }
    }
}
