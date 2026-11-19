/-
  Exact base-10 fixed-scale signed decimal arithmetic modeling C# `System.Decimal`.
  Every operation preserves exact rational semantics m / 10^s, and `truncate` uses
  `Int.tdiv` (truncation toward zero), matching C# `decimal.Truncate` and `(int)decimalVal`.
  Reference: C# `System.Decimal` used throughout `Core.Hooks/Hook.cs`,
  `Core.Commands/CreatureCmd.cs`, `Core.Commands/PowerCmd.cs`, and `Core.Models/*`.
-/

namespace Sts2Model.Core

/-- Exact base-10 decimal `mantissa * 10^(-scale)`. -/
structure Dec where
  mantissa : Int
  scale : Nat := 0
  deriving Repr, DecidableEq, Inhabited

namespace Dec

@[inline] def pow10 (n : Nat) : Int :=
  ((10 ^ n : Nat) : Int)

theorem pow10_pos (n : Nat) : 0 < pow10 n := by
  unfold pow10
  have h : 0 < 10 ^ n := Nat.pow_pos (by decide)
  omega

theorem pow10_nonneg (n : Nat) : 0 ≤ pow10 n :=
  Int.le_of_lt (pow10_pos n)

@[inline] def ofInt (n : Int) : Dec :=
  ⟨n, 0⟩

@[inline] def ofNat (n : Nat) : Dec :=
  ⟨(n : Int), 0⟩

@[inline] def ofScaled (mantissa : Int) (scale : Nat) : Dec :=
  ⟨mantissa, scale⟩

def zero : Dec := ⟨0, 0⟩
def one : Dec := ⟨1, 0⟩

/-- C# `decimal.MaxValue` = 2^96 - 1 = 79228162514264337593543950335m. -/
def maxDecimal : Dec := ⟨79228162514264337593543950335, 0⟩

/-- Non-negativity predicate on raw mantissa (exact for value >= 0 since 10^scale > 0). -/
def nonneg (d : Dec) : Prop := 0 ≤ d.mantissa

instance (d : Dec) : Decidable (nonneg d) :=
  inferInstanceAs (Decidable (0 ≤ d.mantissa))

@[inline] def neg (d : Dec) : Dec :=
  ⟨-d.mantissa, d.scale⟩

@[inline] def add (a b : Dec) : Dec :=
  let s := Nat.max a.scale b.scale
  ⟨a.mantissa * pow10 (s - a.scale) + b.mantissa * pow10 (s - b.scale), s⟩

@[inline] def sub (a b : Dec) : Dec :=
  add a (neg b)

@[inline] def mul (a b : Dec) : Dec :=
  ⟨a.mantissa * b.mantissa, a.scale + b.scale⟩

/-- Exact mathematical equality: a.m * 10^b.s = b.m * 10^a.s. -/
def eqVal (a b : Dec) : Prop :=
  a.mantissa * pow10 b.scale = b.mantissa * pow10 a.scale

/-- Exact mathematical <=: a.m * 10^b.s <= b.m * 10^a.s. -/
def le (a b : Dec) : Prop :=
  a.mantissa * pow10 b.scale ≤ b.mantissa * pow10 a.scale

/-- Exact mathematical <: a.m * 10^b.s < b.m * 10^a.s. -/
def lt (a b : Dec) : Prop :=
  a.mantissa * pow10 b.scale < b.mantissa * pow10 a.scale

instance : LE Dec := ⟨le⟩
instance : LT Dec := ⟨lt⟩

instance (a b : Dec) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.mantissa * pow10 b.scale ≤ b.mantissa * pow10 a.scale))

instance (a b : Dec) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.mantissa * pow10 b.scale < b.mantissa * pow10 a.scale))

instance (a b : Dec) : Decidable (eqVal a b) :=
  inferInstanceAs (Decidable (a.mantissa * pow10 b.scale = b.mantissa * pow10 a.scale))

@[inline] def maxZero (d : Dec) : Dec :=
  if d.mantissa < 0 then zero else d

@[inline] def min (a b : Dec) : Dec :=
  if a ≤ b then a else b

@[inline] def max (a b : Dec) : Dec :=
  if a ≤ b then b else a

@[inline] def clamp (d lo hi : Dec) : Dec :=
  if d < lo then lo else if hi < d then hi else d

/-- Truncate toward zero, matching C# `decimal.Truncate` and `(int)d`. -/
@[inline] def truncate (d : Dec) : Int :=
  Int.tdiv d.mantissa (pow10 d.scale)

/-- Non-negative truncated integer (`Nat`), matching `(int)Math.Max(0m, d)`. -/
@[inline] def toNat (d : Dec) : Nat :=
  Int.toNat (truncate (maxZero d))

private def normalizeAux (m : Int) : Nat → Dec
  | 0 => ⟨m, 0⟩
  | s + 1 =>
      if m % 10 == 0 then
        normalizeAux (m / 10) s
      else
        ⟨m, s + 1⟩

/-- Simplify trailing zeros while preserving value, useful for formatting/printing. -/
def normalize (d : Dec) : Dec :=
  normalizeAux d.mantissa d.scale

/-- Format `Dec` as a clean decimal string (e.g. `12`, `-1.5`, `0.75`). -/
def format (d : Dec) : String :=
  let n := normalize d
  if n.scale == 0 then
    toString n.mantissa
  else
    let sign := if n.mantissa < 0 then "-" else ""
    let absM := Int.natAbs n.mantissa
    let p := 10 ^ n.scale
    let whole := absM / p
    let frac := absM % p
    let fracStrRaw := toString frac
    let padLen := n.scale - fracStrRaw.length
    let pad := String.ofList (List.replicate padLen '0')
    s!"{sign}{whole}.{pad}{fracStrRaw}"

instance : ToString Dec := ⟨format⟩

-- ============================================================================
-- Algebraic and order lemmas
-- ============================================================================

theorem pow10_add (m n : Nat) : pow10 (m + n) = pow10 m * pow10 n := by
  unfold pow10
  rw [Nat.pow_add, Int.natCast_mul]

theorem nonneg_zero : nonneg zero := by
  simp [nonneg, zero]

theorem nonneg_one : nonneg one := by
  simp [nonneg, one]

theorem nonneg_ofInt {n : Int} (h : 0 ≤ n) : nonneg (ofInt n) := h

theorem nonneg_ofNat (n : Nat) : nonneg (ofNat n) :=
  Int.natCast_nonneg n

theorem nonneg_iff_le_zero (d : Dec) : nonneg d ↔ zero ≤ d := by
  change 0 ≤ d.mantissa ↔ (0 : Int) * pow10 d.scale ≤ d.mantissa * pow10 0
  have hp0 : pow10 0 = 1 := by decide
  rw [hp0]
  simp

theorem nonneg_add {a b : Dec} (ha : nonneg a) (hb : nonneg b) : nonneg (add a b) := by
  unfold nonneg add
  have h1 : 0 ≤ a.mantissa * pow10 (Nat.max a.scale b.scale - a.scale) :=
    Int.mul_nonneg ha (pow10_nonneg _)
  have h2 : 0 ≤ b.mantissa * pow10 (Nat.max a.scale b.scale - b.scale) :=
    Int.mul_nonneg hb (pow10_nonneg _)
  exact Int.add_nonneg h1 h2

theorem nonneg_mul {a b : Dec} (ha : nonneg a) (hb : nonneg b) : nonneg (mul a b) := by
  unfold nonneg mul
  exact Int.mul_nonneg ha hb

theorem nonneg_maxZero (d : Dec) : nonneg (maxZero d) := by
  unfold maxZero nonneg
  split
  · simp [zero]
  · rename_i h
    omega

theorem maxZero_eq_self {d : Dec} (hd : nonneg d) : maxZero d = d := by
  unfold maxZero
  have : ¬ d.mantissa < 0 := by
    unfold nonneg at hd
    omega
  simp [this]

theorem truncate_nonneg {d : Dec} (hd : nonneg d) : 0 ≤ truncate d := by
  unfold truncate
  exact Int.tdiv_nonneg hd (pow10_nonneg d.scale)

theorem eqVal_refl (a : Dec) : eqVal a a := rfl

theorem eqVal_symm {a b : Dec} (h : eqVal a b) : eqVal b a :=
  h.symm

theorem eqVal_trans {a b c : Dec} (hab : eqVal a b) (hbc : eqVal b c) : eqVal a c := by
  unfold eqVal at *
  have hbpos : pow10 b.scale ≠ 0 := Int.ne_of_gt (pow10_pos b.scale)
  have h1 : a.mantissa * pow10 c.scale * pow10 b.scale =
            (a.mantissa * pow10 b.scale) * pow10 c.scale := by
    rw [Int.mul_assoc, Int.mul_comm (pow10 c.scale) (pow10 b.scale), ← Int.mul_assoc]
  have h2 : (a.mantissa * pow10 b.scale) * pow10 c.scale =
            (b.mantissa * pow10 a.scale) * pow10 c.scale := by
    rw [hab]
  have h3 : (b.mantissa * pow10 a.scale) * pow10 c.scale =
            (b.mantissa * pow10 c.scale) * pow10 a.scale := by
    rw [Int.mul_assoc, Int.mul_comm (pow10 a.scale) (pow10 c.scale), ← Int.mul_assoc]
  have h4 : (b.mantissa * pow10 c.scale) * pow10 a.scale =
            (c.mantissa * pow10 b.scale) * pow10 a.scale := by
    rw [hbc]
  have h5 : (c.mantissa * pow10 b.scale) * pow10 a.scale =
            c.mantissa * pow10 a.scale * pow10 b.scale := by
    rw [Int.mul_assoc, Int.mul_comm (pow10 b.scale) (pow10 a.scale), ← Int.mul_assoc]
  have heq : a.mantissa * pow10 c.scale * pow10 b.scale =
             c.mantissa * pow10 a.scale * pow10 b.scale :=
    h1.trans (h2.trans (h3.trans (h4.trans h5)))
  exact Int.eq_of_mul_eq_mul_right hbpos heq

theorem add_comm_eqVal (a b : Dec) : eqVal (add a b) (add b a) := by
  unfold eqVal add
  dsimp only
  have hm : Nat.max a.scale b.scale = Nat.max b.scale a.scale := Nat.max_comm a.scale b.scale
  rw [hm]
  congr 1
  rw [Int.add_comm]

theorem mul_comm_eqVal (a b : Dec) : eqVal (mul a b) (mul b a) := by
  unfold eqVal mul
  dsimp only
  rw [Int.mul_comm a.mantissa b.mantissa, Nat.add_comm a.scale b.scale]

theorem add_zero_eqVal (a : Dec) : eqVal (add a zero) a := by
  unfold eqVal add zero
  dsimp only
  have hp0 : pow10 0 = 1 := by decide
  have hm : Nat.max a.scale 0 = a.scale := Nat.max_zero a.scale
  rw [hm, Nat.sub_self, hp0, Int.mul_one, Int.zero_mul, Int.add_zero]

theorem mul_one_eqVal (a : Dec) : eqVal (mul a one) a := by
  unfold eqVal mul one
  simp [Nat.add_zero]

theorem eqVal_add_compat {a₁ a₂ b₁ b₂ : Dec}
    (ha : eqVal a₁ a₂) (hb : eqVal b₁ b₂) : eqVal (add a₁ b₁) (add a₂ b₂) := by
  unfold eqVal at *
  unfold add
  dsimp only
  let s₁ := Nat.max a₁.scale b₁.scale
  let s₂ := Nat.max a₂.scale b₂.scale
  change (a₁.mantissa * pow10 (s₁ - a₁.scale) + b₁.mantissa * pow10 (s₁ - b₁.scale)) * pow10 s₂ =
         (a₂.mantissa * pow10 (s₂ - a₂.scale) + b₂.mantissa * pow10 (s₂ - b₂.scale)) * pow10 s₁
  have ha₁ : a₁.scale ≤ s₁ := Nat.le_max_left _ _
  have hb₁ : b₁.scale ≤ s₁ := Nat.le_max_right _ _
  have ha₂ : a₂.scale ≤ s₂ := Nat.le_max_left _ _
  have hb₂ : b₂.scale ≤ s₂ := Nat.le_max_right _ _
  have hpowA₁ : pow10 (s₁ - a₁.scale) * pow10 a₁.scale = pow10 s₁ := by
    rw [← pow10_add, Nat.sub_add_cancel ha₁]
  have hpowB₁ : pow10 (s₁ - b₁.scale) * pow10 b₁.scale = pow10 s₁ := by
    rw [← pow10_add, Nat.sub_add_cancel hb₁]
  have hpowA₂ : pow10 (s₂ - a₂.scale) * pow10 a₂.scale = pow10 s₂ := by
    rw [← pow10_add, Nat.sub_add_cancel ha₂]
  have hpowB₂ : pow10 (s₂ - b₂.scale) * pow10 b₂.scale = pow10 s₂ := by
    rw [← pow10_add, Nat.sub_add_cancel hb₂]
  have hTermA : a₁.mantissa * pow10 (s₁ - a₁.scale) * pow10 s₂ * pow10 a₁.scale * pow10 a₂.scale =
      a₂.mantissa * pow10 (s₂ - a₂.scale) * pow10 s₁ * pow10 a₁.scale * pow10 a₂.scale := by
    calc a₁.mantissa * pow10 (s₁ - a₁.scale) * pow10 s₂ * pow10 a₁.scale * pow10 a₂.scale
        = (a₁.mantissa * pow10 a₂.scale) * (pow10 (s₁ - a₁.scale) * pow10 a₁.scale) * pow10 s₂ := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = (a₂.mantissa * pow10 a₁.scale) * pow10 s₁ * pow10 s₂ := by rw [ha, hpowA₁]
      _ = (a₂.mantissa * (pow10 (s₂ - a₂.scale) * pow10 a₂.scale)) * pow10 s₁ * pow10 a₁.scale := by
          rw [hpowA₂]; simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = a₂.mantissa * pow10 (s₂ - a₂.scale) * pow10 s₁ * pow10 a₁.scale * pow10 a₂.scale := by
          simp only [Int.mul_left_comm, Int.mul_comm]
  have hA := Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (pow10_pos a₂.scale)) hTermA
  have hA' := Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (pow10_pos a₁.scale)) hA
  have hTermB : b₁.mantissa * pow10 (s₁ - b₁.scale) * pow10 s₂ * pow10 b₁.scale * pow10 b₂.scale =
      b₂.mantissa * pow10 (s₂ - b₂.scale) * pow10 s₁ * pow10 b₁.scale * pow10 b₂.scale := by
    calc b₁.mantissa * pow10 (s₁ - b₁.scale) * pow10 s₂ * pow10 b₁.scale * pow10 b₂.scale
        = (b₁.mantissa * pow10 b₂.scale) * (pow10 (s₁ - b₁.scale) * pow10 b₁.scale) * pow10 s₂ := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = (b₂.mantissa * pow10 b₁.scale) * pow10 s₁ * pow10 s₂ := by rw [hb, hpowB₁]
      _ = (b₂.mantissa * (pow10 (s₂ - b₂.scale) * pow10 b₂.scale)) * pow10 s₁ * pow10 b₁.scale := by
          rw [hpowB₂]; simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = b₂.mantissa * pow10 (s₂ - b₂.scale) * pow10 s₁ * pow10 b₁.scale * pow10 b₂.scale := by
          simp only [Int.mul_left_comm, Int.mul_comm]
  have hB := Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (pow10_pos b₂.scale)) hTermB
  have hB' := Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (pow10_pos b₁.scale)) hB
  rw [Int.add_mul, Int.add_mul, hA', hB']

theorem eqVal_mul_compat {a₁ a₂ b₁ b₂ : Dec}
    (ha : eqVal a₁ a₂) (hb : eqVal b₁ b₂) : eqVal (mul a₁ b₁) (mul a₂ b₂) := by
  unfold eqVal at *
  unfold mul
  dsimp only
  rw [pow10_add, pow10_add]
  calc (a₁.mantissa * b₁.mantissa) * (pow10 a₂.scale * pow10 b₂.scale)
      = (a₁.mantissa * pow10 a₂.scale) * (b₁.mantissa * pow10 b₂.scale) := by
        simp only [Int.mul_assoc, Int.mul_left_comm]
    _ = (a₂.mantissa * pow10 a₁.scale) * (b₂.mantissa * pow10 b₁.scale) := by rw [ha, hb]
    _ = (a₂.mantissa * b₂.mantissa) * (pow10 a₁.scale * pow10 b₁.scale) := by
        simp only [Int.mul_assoc, Int.mul_left_comm]

theorem add_assoc_eqVal (a b c : Dec) : eqVal (add (add a b) c) (add a (add b c)) := by
  unfold eqVal add
  dsimp only
  let sab := Nat.max a.scale b.scale
  let sbc := Nat.max b.scale c.scale
  let sL := Nat.max sab c.scale
  let sR := Nat.max a.scale sbc
  change ((a.mantissa * pow10 (sab - a.scale) + b.mantissa * pow10 (sab - b.scale)) *
            pow10 (sL - sab) + c.mantissa * pow10 (sL - c.scale)) * pow10 sR =
         (a.mantissa * pow10 (sR - a.scale) +
           (b.mantissa * pow10 (sbc - b.scale) + c.mantissa * pow10 (sbc - c.scale)) *
            pow10 (sR - sbc)) * pow10 sL
  have hs : sL = sR := Nat.max_assoc a.scale b.scale c.scale
  have ha_ab : a.scale ≤ sab := Nat.le_max_left _ _
  have hb_ab : b.scale ≤ sab := Nat.le_max_right _ _
  have hsab_L : sab ≤ sL := Nat.le_max_left _ _
  have hc_L : c.scale ≤ sL := Nat.le_max_right _ _
  have hb_bc : b.scale ≤ sbc := Nat.le_max_left _ _
  have hc_bc : c.scale ≤ sbc := Nat.le_max_right _ _
  have ha_R : a.scale ≤ sR := Nat.le_max_left _ _
  have hsbc_R : sbc ≤ sR := Nat.le_max_right _ _
  have h1 : pow10 (sab - a.scale) * pow10 (sL - sab) = pow10 (sL - a.scale) := by
    rw [← pow10_add]; congr 1; omega
  have h2 : pow10 (sab - b.scale) * pow10 (sL - sab) = pow10 (sL - b.scale) := by
    rw [← pow10_add]; congr 1; omega
  have h3 : pow10 (sbc - b.scale) * pow10 (sR - sbc) = pow10 (sR - b.scale) := by
    rw [← pow10_add]; congr 1; omega
  have h4 : pow10 (sbc - c.scale) * pow10 (sR - sbc) = pow10 (sR - c.scale) := by
    rw [← pow10_add]; congr 1; omega
  rw [hs]
  congr 1
  simp only [Int.add_mul, Int.mul_assoc]
  rw [← hs, h1, h2, hs, h3, h4]
  omega

theorem mul_assoc_eqVal (a b c : Dec) : eqVal (mul (mul a b) c) (mul a (mul b c)) := by
  unfold eqVal mul
  dsimp only
  rw [Nat.add_assoc, Int.mul_assoc]
  exact congrArg (· * _) (Int.mul_assoc a.mantissa b.mantissa c.mantissa) |>.symm ▸
    (Int.mul_assoc (a.mantissa * b.mantissa) c.mantissa (pow10 (a.scale + (b.scale + c.scale)))).symm ▸ rfl

theorem le_refl (a : Dec) : a ≤ a := Int.le_refl _

theorem le_trans {a b c : Dec} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  change a.mantissa * pow10 b.scale ≤ b.mantissa * pow10 a.scale at hab
  change b.mantissa * pow10 c.scale ≤ c.mantissa * pow10 b.scale at hbc
  change a.mantissa * pow10 c.scale ≤ c.mantissa * pow10 a.scale
  have hbpos : 0 < pow10 b.scale := pow10_pos b.scale
  have hcpos : 0 ≤ pow10 c.scale := pow10_nonneg c.scale
  have hapos : 0 ≤ pow10 a.scale := pow10_nonneg a.scale
  have h1 : a.mantissa * pow10 c.scale * pow10 b.scale ≤ b.mantissa * pow10 a.scale * pow10 c.scale := by
    have hmul := Int.mul_le_mul_of_nonneg_right hab hcpos
    calc a.mantissa * pow10 c.scale * pow10 b.scale
        = a.mantissa * pow10 b.scale * pow10 c.scale := by
          simp only [Int.mul_assoc, Int.mul_comm (pow10 c.scale) (pow10 b.scale)]
      _ ≤ b.mantissa * pow10 a.scale * pow10 c.scale := hmul
  have h2 : b.mantissa * pow10 a.scale * pow10 c.scale ≤ c.mantissa * pow10 a.scale * pow10 b.scale := by
    have hmul := Int.mul_le_mul_of_nonneg_right hbc hapos
    calc b.mantissa * pow10 a.scale * pow10 c.scale
        = b.mantissa * pow10 c.scale * pow10 a.scale := by
          simp only [Int.mul_assoc, Int.mul_comm (pow10 a.scale) (pow10 c.scale)]
      _ ≤ c.mantissa * pow10 b.scale * pow10 a.scale := hmul
      _ = c.mantissa * pow10 a.scale * pow10 b.scale := by
          simp only [Int.mul_assoc, Int.mul_comm (pow10 b.scale) (pow10 a.scale)]
  exact Int.le_of_mul_le_mul_right (Int.le_trans h1 h2) hbpos

theorem min_le_left (a b : Dec) : min a b ≤ a := by
  unfold min
  split
  · exact le_refl a
  · rename_i h
    change ¬ (a.mantissa * pow10 b.scale ≤ b.mantissa * pow10 a.scale) at h
    change b.mantissa * pow10 a.scale ≤ a.mantissa * pow10 b.scale
    omega

theorem min_le_right (a b : Dec) : min a b ≤ b := by
  unfold min
  split
  · assumption
  · exact le_refl b

theorem le_max_left (a b : Dec) : a ≤ max a b := by
  unfold max
  split
  · assumption
  · exact le_refl a

theorem le_max_right (a b : Dec) : b ≤ max a b := by
  unfold max
  split
  · exact le_refl b
  · rename_i h
    change ¬ (a.mantissa * pow10 b.scale ≤ b.mantissa * pow10 a.scale) at h
    change b.mantissa * pow10 a.scale ≤ a.mantissa * pow10 b.scale
    omega

theorem maxZero_le_self_of_nonneg {d : Dec} (hd : nonneg d) : maxZero d ≤ d := by
  rw [maxZero_eq_self hd]
  exact le_refl d

theorem zero_le_maxZero (d : Dec) : zero ≤ maxZero d := by
  rw [← nonneg_iff_le_zero]
  exact nonneg_maxZero d

theorem le_of_eqVal {a b : Dec} (h : eqVal a b) : a ≤ b := by
  change a.mantissa * pow10 b.scale ≤ b.mantissa * pow10 a.scale
  rw [h]
  exact Int.le_refl _

theorem le_total (a b : Dec) : a ≤ b ∨ b ≤ a := by
  change a.mantissa * pow10 b.scale ≤ b.mantissa * pow10 a.scale ∨
         b.mantissa * pow10 a.scale ≤ a.mantissa * pow10 b.scale
  omega

theorem lt_iff_not_le {a b : Dec} : a < b ↔ ¬ (b ≤ a) := by
  change a.mantissa * pow10 b.scale < b.mantissa * pow10 a.scale ↔
         ¬ (b.mantissa * pow10 a.scale ≤ a.mantissa * pow10 b.scale)
  omega

theorem add_le_add_left {a b c : Dec} (h : a ≤ b) : add c a ≤ add c b := by
  change a.mantissa * pow10 b.scale ≤ b.mantissa * pow10 a.scale at h
  unfold add
  let sa := Nat.max c.scale a.scale
  let sb := Nat.max c.scale b.scale
  change (c.mantissa * pow10 (sa - c.scale) + a.mantissa * pow10 (sa - a.scale)) * pow10 sb ≤
         (c.mantissa * pow10 (sb - c.scale) + b.mantissa * pow10 (sb - b.scale)) * pow10 sa
  have hca : c.scale ≤ sa := Nat.le_max_left _ _
  have haa : a.scale ≤ sa := Nat.le_max_right _ _
  have hcb : c.scale ≤ sb := Nat.le_max_left _ _
  have hbb : b.scale ≤ sb := Nat.le_max_right _ _
  have hpowC₁ : pow10 (sa - c.scale) * pow10 sb * pow10 c.scale = pow10 sa * pow10 sb := by
    calc pow10 (sa - c.scale) * pow10 sb * pow10 c.scale
        = (pow10 (sa - c.scale) * pow10 c.scale) * pow10 sb := by
          simp only [Int.mul_assoc, Int.mul_comm (pow10 sb) (pow10 c.scale)]
      _ = pow10 sa * pow10 sb := by rw [← pow10_add, Nat.sub_add_cancel hca]
  have hpowC₂ : pow10 (sb - c.scale) * pow10 sa * pow10 c.scale = pow10 sa * pow10 sb := by
    calc pow10 (sb - c.scale) * pow10 sa * pow10 c.scale
        = (pow10 (sb - c.scale) * pow10 c.scale) * pow10 sa := by
          simp only [Int.mul_assoc, Int.mul_comm (pow10 sa) (pow10 c.scale)]
      _ = pow10 sb * pow10 sa := by rw [← pow10_add, Nat.sub_add_cancel hcb]
      _ = pow10 sa * pow10 sb := Int.mul_comm _ _
  have hcEq : pow10 (sa - c.scale) * pow10 sb = pow10 (sb - c.scale) * pow10 sa :=
    Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (pow10_pos c.scale)) (hpowC₁.trans hpowC₂.symm)
  have hcTerm : c.mantissa * pow10 (sa - c.scale) * pow10 sb =
                c.mantissa * pow10 (sb - c.scale) * pow10 sa := by
    rw [Int.mul_assoc, hcEq, ← Int.mul_assoc]
  rw [Int.add_mul, Int.add_mul, hcTerm]
  suffices hAB : a.mantissa * pow10 (sa - a.scale) * pow10 sb ≤
                 b.mantissa * pow10 (sb - b.scale) * pow10 sa by omega
  have hmul : a.mantissa * pow10 b.scale * (pow10 (sa - a.scale) * pow10 (sb - b.scale)) ≤
              b.mantissa * pow10 a.scale * (pow10 (sa - a.scale) * pow10 (sb - b.scale)) :=
    Int.mul_le_mul_of_nonneg_right h (Int.mul_nonneg (pow10_nonneg _) (pow10_nonneg _))
  have hl : a.mantissa * pow10 b.scale * (pow10 (sa - a.scale) * pow10 (sb - b.scale)) =
            a.mantissa * pow10 (sa - a.scale) * pow10 sb := by
    have hpb : pow10 (sb - b.scale) * pow10 b.scale = pow10 sb := by
      rw [← pow10_add, Nat.sub_add_cancel hbb]
    calc a.mantissa * pow10 b.scale * (pow10 (sa - a.scale) * pow10 (sb - b.scale))
        = a.mantissa * pow10 (sa - a.scale) * (pow10 (sb - b.scale) * pow10 b.scale) := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = a.mantissa * pow10 (sa - a.scale) * pow10 sb := by rw [hpb]
  have hr : b.mantissa * pow10 a.scale * (pow10 (sa - a.scale) * pow10 (sb - b.scale)) =
            b.mantissa * pow10 (sb - b.scale) * pow10 sa := by
    have hpa : pow10 (sa - a.scale) * pow10 a.scale = pow10 sa := by
      rw [← pow10_add, Nat.sub_add_cancel haa]
    calc b.mantissa * pow10 a.scale * (pow10 (sa - a.scale) * pow10 (sb - b.scale))
        = b.mantissa * pow10 (sb - b.scale) * (pow10 (sa - a.scale) * pow10 a.scale) := by
          simp only [Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
      _ = b.mantissa * pow10 (sb - b.scale) * pow10 sa := by rw [hpa]
  rw [← hl, ← hr]
  exact hmul

theorem mul_le_mul_of_nonneg_right {a b c : Dec} (hab : a ≤ b) (hc : nonneg c) :
    mul a c ≤ mul b c := by
  change a.mantissa * pow10 b.scale ≤ b.mantissa * pow10 a.scale at hab
  change (a.mantissa * c.mantissa) * pow10 (b.scale + c.scale) ≤
         (b.mantissa * c.mantissa) * pow10 (a.scale + c.scale)
  rw [pow10_add b.scale c.scale, pow10_add a.scale c.scale]
  have h1 := Int.mul_le_mul_of_nonneg_right hab (Int.mul_nonneg hc (pow10_nonneg c.scale))
  calc (a.mantissa * c.mantissa) * (pow10 b.scale * pow10 c.scale)
      = a.mantissa * pow10 b.scale * (c.mantissa * pow10 c.scale) := by
        simp only [Int.mul_assoc, Int.mul_left_comm]
    _ ≤ b.mantissa * pow10 a.scale * (c.mantissa * pow10 c.scale) := h1
    _ = (b.mantissa * c.mantissa) * (pow10 a.scale * pow10 c.scale) := by
        simp only [Int.mul_assoc, Int.mul_left_comm]

theorem mul_le_mul_of_nonneg_left {a b c : Dec} (hab : a ≤ b) (hc : nonneg c) :
    mul c a ≤ mul c b := by
  have h := mul_le_mul_of_nonneg_right hab hc
  have hL : eqVal (mul c a) (mul a c) := mul_comm_eqVal c a
  have hR : eqVal (mul b c) (mul c b) := mul_comm_eqVal b c
  exact le_trans (le_of_eqVal hL) (le_trans h (le_of_eqVal hR))

end Dec
end Sts2Model.Core
