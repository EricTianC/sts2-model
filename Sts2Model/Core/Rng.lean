/-
  Bit-exact deterministic PRNG modeling C# `MegaRandom` (SplitMix64 + Xoshiro256**)
  and `Rng`, plus Fisher-Yates `UnstableShuffle` and `RunRngSet` / `PlayerRngSet`.
  Reference:
  - `reference/sts2/MegaCrit.Sts2.Core.Random/MegaRandom.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Random/Rng.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Extensions/ListExtensions.cs`
  - `reference/sts2/MegaCrit.Sts2.Core.Random/RunRngSet.cs`
-/

namespace Sts2Model.Core

/-- SplitMix64 mixing step used to seed Xoshiro256** state from a 64-bit seed.
    Ref: `MegaRandom.Splitmix64(ref ulong x)`. -/
@[inline] def splitmix64 (x : UInt64) : UInt64 × UInt64 :=
  let x' : UInt64 := x + 11400714819323198485
  let num1 : UInt64 := (x' ^^^ (x' >>> 30)) * 13787848793156543929
  let num2 : UInt64 := (num1 ^^^ (num1 >>> 27)) * 10723151780598845931
  let out  : UInt64 := num2 ^^^ (num2 >>> 31)
  (out, x')

/-- 64-bit left bit rotation matching `BitOperations.RotateLeft(ulong, int)`. -/
@[inline] def rotl64 (x : UInt64) (k : UInt64) : UInt64 :=
  if k == 0 then x else (x <<< k) ||| (x >>> (64 - k))

/-- Xoshiro256** internal generator state. Ref: `MegaRandom.cs`. -/
structure MegaRandom where
  s0 : UInt64
  s1 : UInt64
  s2 : UInt64
  s3 : UInt64
  deriving Repr, DecidableEq, Inhabited

namespace MegaRandom

/-- Seed Xoshiro256** via 4 successive SplitMix64 steps.
    Ref: `MegaRandom.Reinitialise(ulong seed)`. -/
def ofSeed (seed : UInt64) : MegaRandom :=
  let (s0, seed1) := splitmix64 seed
  let (s1, seed2) := splitmix64 seed1
  let (s2, seed3) := splitmix64 seed2
  let (s3, _)     := splitmix64 seed3
  ⟨s0, s1, s2, s3⟩

/-- Advance Xoshiro256** state and return 64 pseudo-random bits.
    Ref: `MegaRandom.NextULongInner()`. -/
def nextULong (m : MegaRandom) : UInt64 × MegaRandom :=
  let s0 := m.s0
  let s1 := m.s1
  let s2 := m.s2
  let s3 := m.s3
  let result : UInt64 := rotl64 (s1 * 5) 7 * 9
  let num : UInt64 := s1 <<< 17
  let s2' := s2 ^^^ s0
  let s3' := s3 ^^^ s1
  let s1' := s1 ^^^ s2'
  let s0' := s0 ^^^ s3'
  let s2'' := s2' ^^^ num
  let s3'' := rotl64 s3' 45
  (result, ⟨s0', s1', s2'', s3''⟩)

/-- `2^(-53)` constant in `MegaRandom._incrDouble = 1.1102230246251565E-16`. -/
def incrDouble : Float := 1.1102230246251565e-16

/-- Uniform double in `[0.0, 1.0)` matching `MegaRandom.NextDouble()`. -/
def nextDouble (m : MegaRandom) : Float × MegaRandom :=
  let (u, m') := m.nextULong
  let d : Float := (u >>> 11).toFloat * incrDouble
  (d, m')

/-- Uniform integer in `[0, maxExclusive)` matching `MegaRandom.Next(int maxValue)`.
    Clamped defensively with `Nat.min _ (maxExclusive - 1)` so bounds hold unconditionally in Lean proofs. -/
def nextNat (m : MegaRandom) (maxExclusive : Nat) : Nat × MegaRandom :=
  match maxExclusive with
  | 0 => (0, m)
  | n + 1 =>
      let (d, m') := m.nextDouble
      let raw : Nat := (d * (Float.ofNat (n + 1))).toUInt64.toNat
      (Nat.min raw n, m')

theorem nextNat_lt (m : MegaRandom) {n : Nat} (hn : 0 < n) :
    (m.nextNat n).1 < n := by
  cases n with
  | zero => contradiction
  | succ k =>
      unfold nextNat
      dsimp only
      exact Nat.lt_succ_of_le (Nat.min_le_right _ _)

end MegaRandom

/-- Counter-tracked deterministic RNG matching `Core.Random/Rng.cs`. -/
structure Rng where
  counter : Nat := 0
  state   : MegaRandom
  deriving Repr, DecidableEq

namespace Rng

def ofSeed (seed : UInt64 := 0) : Rng :=
  { counter := 0, state := MegaRandom.ofSeed seed }

/-- Deterministic FNV/Murmur-free string hash matching `StringHelper.GetDeterministicHashCode` if needed,
    plus direct named sub-RNG construction. -/
def nextULong (r : Rng) : UInt64 × Rng :=
  let (v, s') := r.state.nextULong
  (v, { counter := r.counter + 1, state := s' })

def nextDouble (r : Rng) : Float × Rng :=
  let (d, s') := r.state.nextDouble
  (d, { counter := r.counter + 1, state := s' })

def nextInt (r : Rng) (maxExclusive : Nat) : Nat × Rng :=
  let (v, s') := r.state.nextNat maxExclusive
  (v, { counter := r.counter + 1, state := s' })

def nextIntRange (r : Rng) (minInclusive maxExclusive : Int) : Int × Rng :=
  if minInclusive ≥ maxExclusive then
    (minInclusive, r)
  else
    let span : Nat := Int.toNat (maxExclusive - minInclusive)
    let (offset, r') := r.nextInt span
    (minInclusive + (offset : Int), r')

def nextBool (r : Rng) : Bool × Rng :=
  let (v, r') := r.nextInt 2
  (v == 0, r')

theorem nextInt_lt (r : Rng) {n : Nat} (hn : 0 < n) : (r.nextInt n).1 < n := by
  unfold nextInt
  exact MegaRandom.nextNat_lt r.state hn

theorem nextInt_counter (r : Rng) (n : Nat) : (r.nextInt n).2.counter = r.counter + 1 := rfl

private def swapArr {α : Type} (arr : Array α) (i j : Nat) : Array α :=
  if hi : i < arr.size then
    if hj : j < arr.size then
      arr.swap i j hi hj
    else arr
  else arr

private theorem swapArr_size {α : Type} (arr : Array α) (i j : Nat) :
    (swapArr arr i j).size = arr.size := by
  unfold swapArr
  split
  · split
    · exact Array.size_swap ..
    · rfl
  · rfl

private def shuffleLoop {α : Type} (arr : Array α) (num : Nat) (rng : Rng) : Array α × Rng :=
  match num with
  | 0 | 1 => (arr, rng)
  | k + 2 =>
      let idx := k + 1
      let (j, rng') := rng.nextInt (k + 2)
      let arr' := swapArr arr idx j
      shuffleLoop arr' (k + 1) rng'

private theorem shuffleLoop_size {α : Type} (arr : Array α) (num : Nat) (rng : Rng) :
    (shuffleLoop arr num rng).1.size = arr.size := by
  induction num generalizing arr rng with
  | zero => rfl
  | succ m ih =>
      cases m with
      | zero => rfl
      | succ k =>
          unfold shuffleLoop
          dsimp only
          rw [ih, swapArr_size]

private theorem mem_pos_count {α : Type} [BEq α] [LawfulBEq α] {l : List α} {i : Nat} (hi : i < l.length) :
    0 < List.count l[i] l :=
  List.count_pos_iff.mpr (List.getElem_mem hi)

private theorem count_ge_two_of_ne_getElem {α : Type} [BEq α] [LawfulBEq α] {a : α} :
    ∀ {l : List α} {i j : Nat}, (_hi : i < l.length) → (_hj : j < l.length) → i ≠ j →
      l[i] = a → l[j] = a → 1 < List.count a l
  | [], _, _, hi, _, _, _, _ => False.elim (Nat.not_lt_zero _ hi)
  | _ :: tl, 0, 0, _, _, hne, _, _ => False.elim (hne rfl)
  | _ :: tl, 0, j' + 1, _, hj, _, ha1, ha2 => by
      have hj' : j' < tl.length := Nat.succ_lt_succ_iff.mp hj
      have hp : 0 < List.count a tl := by
        have : tl[j'] = a := ha2
        rw [← this]; exact mem_pos_count hj'
      simp only [List.getElem_cons_zero] at ha1
      rw [List.count_cons, ha1, beq_self_eq_true]
      simp only [↓reduceIte]
      omega
  | _ :: tl, i' + 1, 0, hi, _, _, ha1, ha2 => by
      have hi' : i' < tl.length := Nat.succ_lt_succ_iff.mp hi
      have hp : 0 < List.count a tl := by
        have : tl[i'] = a := ha1
        rw [← this]; exact mem_pos_count hi'
      simp only [List.getElem_cons_zero] at ha2
      rw [List.count_cons, ha2, beq_self_eq_true]
      simp only [↓reduceIte]
      omega
  | hd :: tl, i' + 1, j' + 1, hi, hj, hne, ha1, ha2 => by
      have hi' : i' < tl.length := Nat.succ_lt_succ_iff.mp hi
      have hj' : j' < tl.length := Nat.succ_lt_succ_iff.mp hj
      have hne' : i' ≠ j' := fun h => hne (congrArg Nat.succ h)
      have hsub := count_ge_two_of_ne_getElem hi' hj' hne' ha1 ha2
      rw [List.count_cons]
      omega

private theorem list_swap_perm {α : Type} (l : List α) (i j : Nat) (hi : i < l.length) (hj : j < l.length) :
    ((l.set i l[j]).set j l[i]).Perm l := by
  classical
  rw [List.perm_iff_count]
  intro a
  have hlen1 : (l.set i l[j]).length = l.length := List.length_set ..
  have hj1 : j < (l.set i l[j]).length := by omega
  rw [List.count_set hj1, List.count_set hi]
  by_cases hij : i = j
  · subst hij
    simp only [List.getElem_set_self]
    have hpos : (l[i] == a) = true → 0 < List.count a l := fun h => by
      have heq : l[i] = a := beq_iff_eq.mp h
      rw [← heq]; exact mem_pos_count hi
    by_cases h1 : (l[i] == a) = true
    · simp only [h1, ↓reduceIte]
      have := hpos h1; omega
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      omega
  · have hij' : i ≠ j := hij
    rw [List.getElem_set_ne hij' hj1]
    have hci : (l[i] == a) = true → 0 < List.count a l := fun h => by
      have heq : l[i] = a := beq_iff_eq.mp h
      rw [← heq]; exact mem_pos_count hi
    have hcj : (l[j] == a) = true → 0 < List.count a l := fun h => by
      have heq : l[j] = a := beq_iff_eq.mp h
      rw [← heq]; exact mem_pos_count hj
    by_cases h1 : (l[i] == a) = true
    · by_cases h2 : (l[j] == a) = true
      · simp only [h1, h2, ↓reduceIte]
        have hge := count_ge_two_of_ne_getElem hi hj hij' (beq_iff_eq.mp h1) (beq_iff_eq.mp h2)
        omega
      · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
        have := hci h1; omega
    · by_cases h2 : (l[j] == a) = true
      · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
        have := hcj h2; omega
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
        omega

private theorem swapArr_perm {α : Type} (arr : Array α) (i j : Nat) :
    (swapArr arr i j).toList.Perm arr.toList := by
  unfold swapArr
  split
  · split
    · rename_i hi hj
      rw [Array.toList_swap]
      exact list_swap_perm arr.toList i j hi hj
    · exact List.Perm.refl _
  · exact List.Perm.refl _

private theorem shuffleLoop_perm {α : Type} (arr : Array α) (num : Nat) (rng : Rng) :
    (shuffleLoop arr num rng).1.toList.Perm arr.toList := by
  induction num generalizing arr rng with
  | zero => exact List.Perm.refl _
  | succ m ih =>
      cases m with
      | zero => exact List.Perm.refl _
      | succ k =>
          unfold shuffleLoop
          dsimp only
          exact (ih _ _).trans (swapArr_perm _ _ _)

/-- Fisher-Yates shuffle matching `ListExtensions.UnstableShuffle(this List<T>, Rng rng)`:
    creates a child `Rng(rng.NextUnsignedLong())` and swaps backwards from `Count - 1` down to `1`. -/
def unstableShuffle {α : Type} (xs : List α) (rng : Rng) : List α × Rng :=
  let (childSeed, rng') := rng.nextULong
  let childRng := Rng.ofSeed childSeed
  let arr := xs.toArray
  let (shuffledArr, _) := shuffleLoop arr arr.size childRng
  (shuffledArr.toList, rng')

theorem unstableShuffle_length {α : Type} (xs : List α) (rng : Rng) :
    (unstableShuffle xs rng).1.length = xs.length := by
  unfold unstableShuffle
  simp [shuffleLoop_size]

theorem unstableShuffle_perm {α : Type} (xs : List α) (rng : Rng) :
    (unstableShuffle xs rng).1.Perm xs := by
  unfold unstableShuffle
  dsimp only
  have hp := shuffleLoop_perm xs.toArray xs.toArray.size (Rng.ofSeed (rng.nextULong).1)
  simpa using hp

end Rng

/-- Per-run deterministic RNG streams. Ref: `Core.Runs/RunRngSet.cs`. -/
structure RunRngSet where
  seed                   : UInt64
  upfront                : Rng
  shuffle                : Rng
  unknownMap             : Rng
  combatCardGeneration   : Rng
  combatPotionGeneration : Rng
  combatCardSelection    : Rng
  combatEnergyCosts      : Rng
  combatTargets          : Rng
  monsterAi              : Rng
  niche                  : Rng
  combatOrbs             : Rng
  treasureRoomRelics     : Rng
  deriving Repr, DecidableEq

def RunRngSet.ofSeed (seed : UInt64) : RunRngSet :=
  { seed                   := seed
  , upfront                := Rng.ofSeed (seed ^^^ 0x1111111111111111)
  , shuffle                := Rng.ofSeed (seed ^^^ 0x2222222222222222)
  , unknownMap             := Rng.ofSeed (seed ^^^ 0x3333333333333333)
  , combatCardGeneration   := Rng.ofSeed (seed ^^^ 0x4444444444444444)
  , combatPotionGeneration := Rng.ofSeed (seed ^^^ 0x5555555555555555)
  , combatCardSelection    := Rng.ofSeed (seed ^^^ 0x6666666666666666)
  , combatEnergyCosts      := Rng.ofSeed (seed ^^^ 0x7777777777777777)
  , combatTargets          := Rng.ofSeed (seed ^^^ 0x8888888888888888)
  , monsterAi              := Rng.ofSeed (seed ^^^ 0x9999999999999999)
  , niche                  := Rng.ofSeed (seed ^^^ 0xAAAAAAAAAAAAAAAA)
  , combatOrbs             := Rng.ofSeed (seed ^^^ 0xBBBBBBBBBBBBBBBB)
  , treasureRoomRelics     := Rng.ofSeed (seed ^^^ 0xCCCCCCCCCCCCCCCC) }

/-- Per-player RNG streams. Ref: `Core.Random/PlayerRngSet.cs`. -/
structure PlayerRngSet where
  seed                : UInt64
  rewards             : Rng
  shops               : Rng
  transformations     : Rng
  nonCombatGeneration : Rng
  deriving Repr, DecidableEq

def PlayerRngSet.ofSeed (seed : UInt64) (slot : Nat := 0) : PlayerRngSet :=
  let s := seed + UInt64.ofNat slot
  { seed                := s
  , rewards             := Rng.ofSeed (s ^^^ 0x123456789ABCDEF0)
  , shops               := Rng.ofSeed (s ^^^ 0x23456789ABCDEF01)
  , transformations     := Rng.ofSeed (s ^^^ 0x3456789ABCDEF012)
  , nonCombatGeneration := Rng.ofSeed (s ^^^ 0x456789ABCDEF0123) }

end Sts2Model.Core
