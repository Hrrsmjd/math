/-
  IntMulKappa.lean

  Machine-checked arithmetic behind the improved constant `κ` in the paper on integer
  multiplication below `n log n`.

  * Core Lean 4 only (no Mathlib, no Batteries); tested with Lean 4.34.1.
  * No `sorry`, `admit`, `native_decide`, or new axioms.  Closed numerical facts are checked
    by `decide` (elaborator + kernel) or `decide +kernel` (kernel only; the kernel has
    GMP-accelerated `Nat` arithmetic, which also makes core `Rat` comparisons cheap).
  * Statements containing astronomically large powers (e.g. `s ^ (5 * 2 ^ 36)`) are NEVER
    evaluated.  They are proved only by instantiating a general lemma (`rate_cert`) whose
    conclusion matches the statement syntactically; the only thing evaluated is a small
    certificate (36 to 50 truncated squarings of numbers of at most ~6300 bits).
  * `#print axioms` for every main theorem is at the end of the file.
-/

namespace IntMulKappa

/-!
## Section 1. Network counts

Size parameters of the two Boolean networks, as functions of the block parameter `h`
(all in `Nat`, with truncated subtraction and floor division, exactly as written):

* `v = C(h,3)`, `N = v^3`, `m = h^3`, `I = 3 v^2`;
* the bit (address-interchange) network: `z_b = 3 C(h-3,2)`, width `W_b`, `L_b`, size `s_b`;
* the complex (phase) network: `z_c = C(h-3,3) + 3(h-3)`, width `W_c`, `L_c`, size `s_c`.

Certified: (a) the values printed in the paper for `h = 100`; (b) all the counts at
`h = 46`, the relations between them, and the deficit identity
`η_b := (N - 2 L_b) / (W_b m) = 9 / 43518487588` at `h = 46`.
-/

/-- `v h = C(h,3)`. -/
def v (h : Nat) : Nat := h * (h - 1) * (h - 2) / 6
/-- `N h = v^3`. -/
def N (h : Nat) : Nat := v h ^ 3
/-- `m h = h^3`. -/
def m (h : Nat) : Nat := h ^ 3
/-- `I h = 3 v^2`. -/
def I (h : Nat) : Nat := 3 * v h ^ 2

/-- Bit network: `z_b = 3 C(h-3,2)`. -/
def zb (h : Nat) : Nat := 3 * ((h - 3) * (h - 4) / 2)
/-- Bit network width `W_b = 2N + I (v z_b + h)`. -/
def Wb (h : Nat) : Nat := 2 * N h + I h * (v h * zb h + h)
/-- Bit network: `L_b = I h^2`. -/
def Lb (h : Nat) : Nat := I h * h * h
/-- Bit network size `s_b = W_b m - N + 2 L_b`. -/
def sb (h : Nat) : Nat := Wb h * m h - N h + 2 * Lb h

/-- Complex network: `z_c = C(h-3,3) + 3(h-3)`. -/
def zc (h : Nat) : Nat := (h - 3) * (h - 4) * (h - 5) / 6 + 3 * (h - 3)
/-- Complex network width `W_c = 2N + I (v z_c + (h+1))`. -/
def Wc (h : Nat) : Nat := 2 * N h + I h * (v h * zc h + (h + 1))
/-- Complex network: `L_c = I (h+1) h`. -/
def Lc (h : Nat) : Nat := I h * (h + 1) * h
/-- Complex network size `s_c = W_c m - 2N + 2 L_c`. -/
def sc (h : Nat) : Nat := Wc h * m h - 2 * N h + 2 * Lc h

/-- (a) Sanity check: the values printed in the paper for `h = 100`. -/
theorem printed_values_h100 :
    Wb 100 = 177176569091445000000 ∧
    sb 100 = 177176569088785861287000000 ∧
    Wc 100 = 1873807244643542670000 ∧
    sc 100 = 1873807244636671267308000000 := by
  decide

/-- (b) The bit-network counts at `h = 46`. -/
theorem counts_h46 :
    v 46 = 15180 ∧ N 46 = 3497963832000 ∧ m 46 = 97336 ∧ zb 46 = 2709 ∧
    Wb 46 = 28434979789999200 ∧ Lb 46 = 1462784875200 ∧
    sb 46 = 2767747192266968049600 := by
  decide

/-- (b) Relations at `h = 46`: `L_b/N = 23/55 < 1/2`, `s_b = W_b m - (N - 2 L_b) < W_b m`. -/
theorem relations_h46 :
    55 * Lb 46 = 23 * N 46 ∧ 2 * Lb 46 < N 46 ∧
    sb 46 + N 46 = Wb 46 * m 46 + 2 * Lb 46 ∧ sb 46 < Wb 46 * m 46 := by
  decide

/-- (b) Deficit identity at `h = 46`: `η_b = (N - 2 L_b)/(W_b m) = 9/43518487588`,
i.e. `s_b / (W_b m) = 1 - 9/43518487588`. -/
theorem eta_b_h46 : (N 46 - 2 * Lb 46) * 43518487588 = 9 * (Wb 46 * m 46) := by
  decide

/-!
## Section 2. Exponent certificates

Write `X = W * m`, `Y = s` and `M = m`.  For `p, q, n : Nat`, the integer inequality
`Y ^ (q * 2^n) * M ^ p < X ^ (q * 2^n)` is the integer form of
`s / W < m ^ (1 - p / (q * 2^n))`: dividing both sides by `m` and raising them to the power
`q 2^n` (everything is positive), the latter is equivalent to
`(s / (W m)) ^ (q 2^n) < m ^ (-p)`, i.e. to `s ^ (q 2^n) * m ^ p < (W m) ^ (q 2^n)`.
So each instance below certifies that `τ = 1 - p / (q 2^n)` is an admissible exponent.

The exponents (`5 * 2^36`, `2^40`, `2^50`) are far too large to evaluate.  We use repeated
squaring with truncation at a scale `Q`: `ySeq Q X Y i` is a lower bound for
`Q * (X/Y)^(2^i)` (`ySeq_spec`), so the small check `Q^q * M^p < (ySeq Q X Y n)^q`, run by
`decide +kernel` (`n` truncated squarings), implies the huge inequality (`rate_cert`).
The huge statements are then closed by applying `rate_cert`; they are never reduced.

All instances use `Q = 2^160`.  Truncation costs a relative error of about `2^-160` per
step, amplified by at most `2^n ≤ 2^50`, which is negligible against the slack of each
certificate (recorded in the docstrings as `rhs / lhs` of the checked inequality `hfin`).
-/

/-- Truncated repeated squaring: `ySeq Q X Y i ≈ Q * (X / Y) ^ (2 ^ i)`, rounded down. -/
def ySeq (Q X Y : Nat) : Nat → Nat
  | 0 => Q * X / Y
  | i + 1 => ySeq Q X Y i ^ 2 / Q

/-- `ySeq` is a lower bound: `ySeq Q X Y i * Y^(2^i) ≤ Q * X^(2^i)`.
(The hypothesis `0 < Y` is kept from the specification but is not needed, hence `_hY`.) -/
theorem ySeq_spec (Q X Y : Nat) (hQ : 0 < Q) (_hY : 0 < Y) :
    ∀ i, ySeq Q X Y i * Y ^ (2 ^ i) ≤ Q * X ^ (2 ^ i) := by
  intro i
  induction i with
  | zero =>
    show Q * X / Y * Y ^ 1 ≤ Q * X ^ 1
    rw [Nat.pow_one, Nat.pow_one]
    exact Nat.div_mul_le_self (Q * X) Y
  | succ i ih =>
    -- `y' = y^2 / Q` satisfies `y' * Q ≤ y^2`
    have hdiv : ySeq Q X Y (i + 1) * Q ≤ ySeq Q X Y i ^ 2 := Nat.div_mul_le_self _ _
    have hsq : 2 ^ (i + 1) = 2 ^ i * 2 := Nat.pow_succ 2 i
    rw [hsq, Nat.pow_mul, Nat.pow_mul]
    -- cancel one factor `Q`
    refine Nat.le_of_mul_le_mul_left ?_ hQ
    calc Q * (ySeq Q X Y (i + 1) * (Y ^ 2 ^ i) ^ 2)
        = ySeq Q X Y (i + 1) * Q * (Y ^ 2 ^ i) ^ 2 := by
          rw [← Nat.mul_assoc, Nat.mul_comm Q]
      _ ≤ ySeq Q X Y i ^ 2 * (Y ^ 2 ^ i) ^ 2 := Nat.mul_le_mul_right _ hdiv
      _ = (ySeq Q X Y i * Y ^ 2 ^ i) ^ 2 := (Nat.mul_pow _ _ _).symm
      _ ≤ (Q * X ^ 2 ^ i) ^ 2 := Nat.pow_le_pow_left ih 2
      _ = Q * (Q * (X ^ 2 ^ i) ^ 2) := by
          rw [Nat.mul_pow, Nat.pow_two Q, Nat.mul_assoc]

/-- **Rate certificate.**  If `Q^q * M^p < (ySeq Q X Y n)^q` (a small, checkable
inequality), then `Y^(q 2^n) * M^p < X^(q 2^n)`. -/
theorem rate_cert (Q X Y M p q n : Nat) (hQ : 0 < Q) (hY : 0 < Y)
    (hfin : Q ^ q * M ^ p < ySeq Q X Y n ^ q) :
    Y ^ (q * 2 ^ n) * M ^ p < X ^ (q * 2 ^ n) := by
  have hs := ySeq_spec Q X Y hQ hY n
  -- raise `ySeq_spec` to the power `q`
  have hq : ySeq Q X Y n ^ q * Y ^ (q * 2 ^ n) ≤ Q ^ q * X ^ (q * 2 ^ n) := by
    have := Nat.pow_le_pow_left hs q
    rw [Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul', ← Nat.pow_mul'] at this
    exact this
  have hYpos : 0 < Y ^ (q * 2 ^ n) := Nat.pow_pos hY
  have key : Q ^ q * (Y ^ (q * 2 ^ n) * M ^ p) < Q ^ q * X ^ (q * 2 ^ n) :=
    calc Q ^ q * (Y ^ (q * 2 ^ n) * M ^ p)
        = Q ^ q * M ^ p * Y ^ (q * 2 ^ n) := by
          rw [Nat.mul_comm (Y ^ (q * 2 ^ n)), Nat.mul_assoc]
      _ < ySeq Q X Y n ^ q * Y ^ (q * 2 ^ n) := Nat.mul_lt_mul_of_pos_right hfin hYpos
      _ ≤ Q ^ q * X ^ (q * 2 ^ n) := hq
  exact Nat.lt_of_mul_lt_mul_left key

/-- `τ_B` (Set B): at `h = 46`, `s_b / W_b < m ^ τ` with `τ = 1 - (6/5)·2^-36`.
Certificate slack ≈ 8.5; the squarings involve numbers of at most 341 bits. -/
theorem tau_B : sb 46 ^ (5 * 2 ^ 36) * m 46 ^ 6 < (Wb 46 * m 46) ^ (5 * 2 ^ 36) :=
  rate_cert (2 ^ 160) (Wb 46 * m 46) (sb 46) (m 46) 6 5 36
    (by decide) (by decide) (by decide +kernel)

/-- `τ_A` (Set A): at `h = 46`, `s_b / W_b < m ^ τ` with `τ = 1 - 2^-36`.
Certificate slack ≈ 15.3; squarings of at most 341 bits. -/
theorem tau_A : sb 46 ^ (1 * 2 ^ 36) * m 46 ^ 1 < (Wb 46 * m 46) ^ (1 * 2 ^ 36) :=
  rate_cert (2 ^ 160) (Wb 46 * m 46) (sb 46) (m 46) 1 1 36
    (by decide) (by decide) (by decide +kernel)

/-- `h = 100` bit network: `s_b / W_b < m ^ τ` with `τ = 1 - 2^-40`.
Certificate slack ≈ 14.7; squarings of at most 344 bits. -/
theorem tau_100 : sb 100 ^ (1 * 2 ^ 40) * m 100 ^ 1 < (Wb 100 * m 100) ^ (1 * 2 ^ 40) :=
  rate_cert (2 ^ 160) (Wb 100 * m 100) (sb 100) (m 100) 1 1 40
    (by decide) (by decide) (by decide +kernel)

/-- The paper's `σ`: `h = 100` complex network, `s_c / W_c < m ^ σ` with `σ = 1 - 2^-50`.
Certificate slack ≈ 2^5937; squarings of at most 6277 bits. -/
theorem sigma_paper : sc 100 ^ (1 * 2 ^ 50) * m 100 ^ 1 < (Wc 100 * m 100) ^ (1 * 2 ^ 50) :=
  rate_cert (2 ^ 160) (Wc 100 * m 100) (sc 100) (m 100) 1 1 50
    (by decide) (by decide) (by decide +kernel)

/-!
## Section 3. Guard-width depth recursion

`depth_unroll`: if a cost `A j` (at depth `j`) satisfies `A j ≤ 8 mm^j` at leaves and
`A (j+1) ≤ μ A j + E` at internal nodes, where `2 ≤ μ ≤ mm^C`, then
`A j + E ≤ (8 + E) mm^(C j)` for every `j`; i.e. the guard exponent is `C`.
`pow_add_le` / `sum_pow_le` are the superadditivity facts `Σ aᵢ^C ≤ (Σ aᵢ)^C` (`C ≥ 1`).
The side conditions for `h = 100` are checked by `decide`:
`μ = s_c(100) ≤ m(100)^5` (guard exponent `C₁ = 5`) and `μ = m(100) + 6·100 ≤ m(100)^2`
(guard exponent `C₁ = 2`).
-/

/-- Superadditivity of `x ↦ x^C` for `C ≥ 1`. -/
theorem pow_add_le (a b C : Nat) (hC : 1 ≤ C) : a ^ C + b ^ C ≤ (a + b) ^ C := by
  obtain ⟨D, rfl⟩ : ∃ D, C = D + 1 := ⟨C - 1, by omega⟩
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.mul_add]
  exact Nat.add_le_add
    (Nat.mul_le_mul_right a (Nat.pow_le_pow_left (Nat.le_add_right a b) D))
    (Nat.mul_le_mul_right b (Nat.pow_le_pow_left (Nat.le_add_left b a) D))

/-- `Σ aᵢ^C ≤ (Σ aᵢ)^C` for `C ≥ 1`. -/
theorem sum_pow_le (l : List Nat) (C : Nat) (hC : 1 ≤ C) :
    (l.map (· ^ C)).sum ≤ l.sum ^ C := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.le_trans (Nat.add_le_add_left ih _) (pow_add_le x l.sum C hC)

/-- **Depth unrolling.**  Invariant: `A j + E ≤ (8 + E) * mm^(C j)`. -/
theorem depth_unroll (mm C E μ : Nat) (A : Nat → Nat) (leaf : Nat → Prop)
    (hm : 1 ≤ mm) (hC : 1 ≤ C) (hμ2 : 2 ≤ μ) (hμ : μ ≤ mm ^ C)
    (hleaf : ∀ j, leaf j → A j ≤ 8 * mm ^ j)
    (hint : ∀ j, ¬ leaf (j + 1) → A (j + 1) ≤ μ * A j + E)
    (h0 : leaf 0) : ∀ j, A j + E ≤ (8 + E) * mm ^ (C * j) := by
  -- the leaf case at any depth
  have hleafcase : ∀ j, leaf j → A j + E ≤ (8 + E) * mm ^ (C * j) := by
    intro j hj
    have h1 : mm ^ j ≤ mm ^ (C * j) := Nat.pow_le_pow_right hm (Nat.le_mul_of_pos_left j hC)
    have h2 : 1 ≤ mm ^ (C * j) := Nat.one_le_pow _ _ hm
    calc A j + E ≤ 8 * mm ^ (C * j) + E * mm ^ (C * j) :=
          Nat.add_le_add (Nat.le_trans (hleaf j hj) (Nat.mul_le_mul_left 8 h1))
            (Nat.le_mul_of_pos_right E h2)
      _ = (8 + E) * mm ^ (C * j) := (Nat.add_mul 8 E _).symm
  intro j
  induction j with
  | zero => exact hleafcase 0 h0
  | succ j ih =>
    by_cases hl : leaf (j + 1)
    · exact hleafcase (j + 1) hl
    · have h2E : 2 * E ≤ μ * E := Nat.mul_le_mul_right E hμ2
      calc A (j + 1) + E ≤ μ * A j + E + E := Nat.add_le_add_right (hint j hl) E
        _ ≤ μ * A j + μ * E := by omega
        _ = μ * (A j + E) := (Nat.mul_add μ (A j) E).symm
        _ ≤ mm ^ C * ((8 + E) * mm ^ (C * j)) := Nat.mul_le_mul hμ ih
        _ = (8 + E) * mm ^ (C * (j + 1)) := by
          rw [Nat.mul_succ, Nat.pow_add, Nat.mul_left_comm, Nat.mul_comm (mm ^ C)]

/-- Numerical side conditions for `h = 100`: `2 ≤ s_c(100) ≤ m(100)^5` (route `C₁ = 5`) and
`m(100) + 6·100 ≤ m(100)^2` (route `C₁ = 2`). -/
theorem guard_instances_h100 :
    2 ≤ sc 100 ∧ sc 100 ≤ m 100 ^ 5 ∧ m 100 + 6 * 100 ≤ m 100 ^ 2 := by
  decide

/-- Route `C₁ = 5` at `h = 100`: internal step factor `μ = s_c(100)`, base `mm = m(100)`. -/
theorem depth_unroll_C5 (E : Nat) (A : Nat → Nat) (leaf : Nat → Prop)
    (hleaf : ∀ j, leaf j → A j ≤ 8 * m 100 ^ j)
    (hint : ∀ j, ¬ leaf (j + 1) → A (j + 1) ≤ sc 100 * A j + E) (h0 : leaf 0) :
    ∀ j, A j + E ≤ (8 + E) * m 100 ^ (5 * j) :=
  depth_unroll (m 100) 5 E (sc 100) A leaf (by decide) (by decide)
    guard_instances_h100.1 guard_instances_h100.2.1 hleaf hint h0

/-- Route `C₁ = 2` at `h = 100`: internal step factor `μ = m(100) + 6·100`. -/
theorem depth_unroll_C2 (E : Nat) (A : Nat → Nat) (leaf : Nat → Prop)
    (hleaf : ∀ j, leaf j → A j ≤ 8 * m 100 ^ j)
    (hint : ∀ j, ¬ leaf (j + 1) → A (j + 1) ≤ (m 100 + 6 * 100) * A j + E) (h0 : leaf 0) :
    ∀ j, A j + E ≤ (8 + E) * m 100 ^ (2 * j) :=
  depth_unroll (m 100) 2 E (m 100 + 6 * 100) A leaf (by decide) (by decide) (by decide)
    guard_instances_h100.2.2 hleaf hint h0

/-!
## Section 4. Chain total-variation potential

The label-dimension graph of the three-stage network (one invocation per stage, stages
`j = 0, 1, 2`).  `gate j t` stands for the gates executed at time `t = 0..7` of stage `j`
(schedule (2) of the paper); all of them carry the label dimension `dim h (gate j t)` read off
from table (6) and Lemma 6 (with the one-dimensional factor `Q` suppressed and `a = h^j`).
The edges are those of the four kinds of wire: the physical X and Y data wires (which run
through all three stages), and the centre and side scratch wires of each stage.  A dependency
chain changes wires only at gates, where all touched wires share one label, so its sequence of
vertices is a path in this graph.  Every vertex `x` has a level `k x`, and the potential is
`phi h x = dim h x + 2 h k(x)`.

Certified (for `h = 25, 46, 100`): along every edge `(u, w)`,
`|dim u - dim w| + phi u ≤ phi w`, and `phi x ≤ h^3 + 6h` for every vertex.  By telescoping
(`tv_add_phi_le`) the total variation `tv` of the dimension along any path is at most
`h^3 + 6h` (`chain_tv_bound`), and an explicit path attains it (`extremal_tv`).
-/

section ChainPotential

/-- Vertices of the three-stage chain. -/
inductive V
  | xsrc
  | ysrc
  | gate (j : Fin 3) (t : Fin 8)
  | csrc (j : Fin 3)
  | ssrc (j : Fin 3)
  | csink (j : Fin 3)
  | ssink (j : Fin 3)
  | xsink
  | ysink
  deriving DecidableEq

open V

/-- Dimension carried at a vertex; at stage `j` put `a = h^j`. -/
def dim (h : Nat) : V → Nat
  | gate j t =>
    let a := h ^ j.val
    match t.val with
    | 0 => a - 1
    | 1 => (a - 1) * h
    | 2 => (a - 1) * h + 1
    | 3 => a * h
    | 4 => (a - 1) * h
    | 5 => (a - 1) * h + h - 1
    | 6 => a * h
    | _ => a * h            -- t = 7
  | xsrc => 1
  | ysrc => 0
  | csrc _ => 0
  | ssrc _ => 0
  | csink _ => h ^ 3
  | ssink _ => h ^ 3
  | xsink => h ^ 3
  | ysink => h ^ 3 - 1

/-- The level `k(x)`: ports `0..3` of stage `j` are at level `j`, ports `4..7` at `j + 1`. -/
def k : V → Nat
  | xsrc => 0
  | ysrc => 0
  | csrc j => j.val
  | ssrc j => j.val
  | gate j t => if t.val ≤ 3 then j.val else j.val + 1
  | csink j => j.val + 1
  | ssink j => j.val + 1
  | xsink => 3
  | ysink => 3

/-- The potential `phi h x = dim h x + 2 h k(x)`. -/
def phi (h : Nat) (x : V) : Nat := dim h x + 2 * h * k x

/-- `dist a b = |a - b|` on `Nat`. -/
def dist (a b : Nat) : Nat := (a - b) + (b - a)

/-- The three stages. -/
def stages : List (Fin 3) := [0, 1, 2]

/-- X wire: `xsrc → g0.2`, inside each stage `2 → 3 → 6 → 7`, then `g_j.7 → g_{j+1}.2`,
`g2.7 → xsink`. -/
def xWire : List (V × V) :=
  [(xsrc, gate 0 2)] ++
  stages.flatMap (fun j => [(gate j 2, gate j 3), (gate j 3, gate j 6), (gate j 6, gate j 7)]) ++
  [(gate 0 7, gate 1 2), (gate 1 7, gate 2 2), (gate 2 7, xsink)]

/-- Y wire: `ysrc → g0.0`, inside each stage `0 → 1 → 4 → 5`, then `g_j.5 → g_{j+1}.0`,
`g2.5 → ysink`. -/
def yWire : List (V × V) :=
  [(ysrc, gate 0 0)] ++
  stages.flatMap (fun j => [(gate j 0, gate j 1), (gate j 1, gate j 4), (gate j 4, gate j 5)]) ++
  [(gate 0 5, gate 1 0), (gate 1 5, gate 2 0), (gate 2 5, ysink)]

/-- Centre wires: `csrc j → 1 → 3 → 4 → 6 → csink j`. -/
def centreWires : List (V × V) :=
  stages.flatMap (fun j => [(csrc j, gate j 1), (gate j 1, gate j 3), (gate j 3, gate j 4),
    (gate j 4, gate j 6), (gate j 6, csink j)])

/-- Side wires: `ssrc j → 0 → 2 → 5 → 7 → ssink j`. -/
def sideWires : List (V × V) :=
  stages.flatMap (fun j => [(ssrc j, gate j 0), (gate j 0, gate j 2), (gate j 2, gate j 5),
    (gate j 5, gate j 7), (gate j 7, ssink j)])

/-- All 56 directed edges of the chain. -/
def edges : List (V × V) := xWire ++ yWire ++ centreWires ++ sideWires

/-- The eight ports of a gate. -/
def ports : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- Explicit list of all 40 vertices. -/
def allV : List V :=
  [xsrc, ysrc, xsink, ysink] ++
  stages.flatMap (fun j => [csrc j, ssrc j, csink j, ssink j] ++ ports.map (gate j))

/-- Sanity check of the two docstrings above. -/
theorem edges_allV_length : edges.length = 56 ∧ allV.length = 40 := by decide

/-- `allV` really lists every vertex. -/
theorem mem_allV : ∀ x : V, x ∈ allV := by
  intro x
  cases x with
  | gate j t => revert j t; decide
  | csrc j => revert j; decide
  | ssrc j => revert j; decide
  | csink j => revert j; decide
  | ssink j => revert j; decide
  | _ => decide

/-- Total variation of the dimension along a vertex sequence. -/
def tv (h : Nat) : List V → Nat
  | [] => 0
  | [_] => 0
  | u :: w :: rest => dist (dim h u) (dim h w) + tv h (w :: rest)

/-- A path: every pair of consecutive vertices is an edge. -/
def IsPath : List V → Prop
  | [] => True
  | [_] => True
  | u :: w :: rest => (u, w) ∈ edges ∧ IsPath (w :: rest)

instance instDecidableIsPath : (p : List V) → Decidable (IsPath p)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | u :: w :: rest =>
    have := instDecidableIsPath (w :: rest)
    inferInstanceAs (Decidable ((u, w) ∈ edges ∧ IsPath (w :: rest)))

/-- **Telescoping.**  If `phi h` grows along every edge by at least the jump of `dim h`, then
for every nonempty path `p`: `tv h p + phi h (head p) ≤ phi h (last p)`. -/
theorem tv_add_phi_le (h : Nat)
    (hE : ∀ e ∈ edges, dist (dim h e.1) (dim h e.2) + phi h e.1 ≤ phi h e.2) :
    ∀ (p : List V) (hne : p ≠ []), IsPath p →
      tv h p + phi h (p.head hne) ≤ phi h (p.getLast hne) := by
  intro p
  induction p with
  | nil => intro hne; exact absurd rfl hne
  | cons x rest ih =>
    intro _ hp
    cases rest with
    | nil => simp [tv]
    | cons y rest' =>
      obtain ⟨hxy, hrest⟩ := hp
      have h1 := hE (x, y) hxy
      have h2 := ih (List.cons_ne_nil y rest') hrest
      simp only [tv, List.head_cons, List.getLast_cons_cons] at h1 h2 ⊢
      omega

/-- General bound: if the edge and vertex checks hold for `h`, every path has
`tv h p ≤ h^3 + 6h`. -/
theorem tv_le_of_checks (h : Nat)
    (hE : ∀ e ∈ edges, dist (dim h e.1) (dim h e.2) + phi h e.1 ≤ phi h e.2)
    (hV : ∀ x ∈ allV, phi h x ≤ h ^ 3 + 6 * h) :
    ∀ p, IsPath p → tv h p ≤ h ^ 3 + 6 * h := by
  intro p hp
  cases p with
  | nil => simp [tv]
  | cons x rest =>
    have h1 := tv_add_phi_le h hE (x :: rest) (List.cons_ne_nil x rest) hp
    have h2 := hV _ (mem_allV ((x :: rest).getLast (List.cons_ne_nil x rest)))
    omega

/-- Edge checks for `h = 25, 46, 100`. -/
theorem edges_ok_25 :
    ∀ e ∈ edges, dist (dim 25 e.1) (dim 25 e.2) + phi 25 e.1 ≤ phi 25 e.2 := by decide +kernel
theorem edges_ok_46 :
    ∀ e ∈ edges, dist (dim 46 e.1) (dim 46 e.2) + phi 46 e.1 ≤ phi 46 e.2 := by decide +kernel
theorem edges_ok_100 :
    ∀ e ∈ edges, dist (dim 100 e.1) (dim 100 e.2) + phi 100 e.1 ≤ phi 100 e.2 := by
  decide +kernel

/-- Vertex checks for `h = 25, 46, 100`. -/
theorem vertices_ok_25 : ∀ x ∈ allV, phi 25 x ≤ 25 ^ 3 + 6 * 25 := by decide +kernel
theorem vertices_ok_46 : ∀ x ∈ allV, phi 46 x ≤ 46 ^ 3 + 6 * 46 := by decide +kernel
theorem vertices_ok_100 : ∀ x ∈ allV, phi 100 x ≤ 100 ^ 3 + 6 * 100 := by decide +kernel

/-- **Chain total-variation bound** at `h = 100`. -/
theorem chain_tv_bound (p : List V) (hp : IsPath p) : tv 100 p ≤ 100 ^ 3 + 6 * 100 :=
  tv_le_of_checks 100 edges_ok_100 vertices_ok_100 p hp

/-- The same bound at `h = 25`. -/
theorem chain_tv_bound_25 (p : List V) (hp : IsPath p) : tv 25 p ≤ 25 ^ 3 + 6 * 25 :=
  tv_le_of_checks 25 edges_ok_25 vertices_ok_25 p hp

/-- The same bound at `h = 46`. -/
theorem chain_tv_bound_46 (p : List V) (hp : IsPath p) : tv 46 p ≤ 46 ^ 3 + 6 * 46 :=
  tv_le_of_checks 46 edges_ok_46 vertices_ok_46 p hp

/-- A path attaining the bound. -/
def extremalPath : List V :=
  [csrc 0, gate 0 1, gate 0 3, gate 0 4, gate 0 5, gate 1 0, gate 1 1, gate 1 3, gate 1 4,
   gate 1 6, gate 1 7, gate 2 2, gate 2 3, gate 2 4, gate 2 6, csink 2]

/-- The extremal path is a path, and its total variation is exactly `h^3 + 6h`
(`h = 100, 25, 46`): the bound of `chain_tv_bound` is sharp. -/
theorem extremal_tv :
    IsPath extremalPath ∧ tv 100 extremalPath = 100 ^ 3 + 6 * 100 ∧
    tv 25 extremalPath = 25 ^ 3 + 6 * 25 ∧ tv 46 extremalPath = 46 ^ 3 + 6 * 46 := by
  decide

end ChainPotential

/-!
## Section 5. Parameters and margins

Exact rational arithmetic (core `Rat`, `decide +kernel`).  For each parameter set we check
the structural conditions

  `1 - T < λ`, `1 - S < λ`, `λ < 1`, `(1 - T)(1 + c/β) < λ`, `λ < λ'`, `(1 - S) + β S < λ'`,
  `λ' < 1`, `ε C₁ < 1`, `0 < δ < 1/8`, `ε < 1/3`, `0 < c`, `0 < β < 1`

(where `τ = 1 - T`, `σ = 1 - S`), and that the margins `g1, …, g7` all exceed `κ`
(for the paper's set: that the smallest margin is `g2 = 2^-181`).
Each set is a namespace with a single bundled theorem `certified`.
-/

/-! ### Set B: `κ = 2^-74`
(`τ = 1 - T` with `T = (6/5)·2^-36` as in `tau_B`; guard exponent `C₁ = 5` as in
`depth_unroll_C5`.) -/
namespace SetB
def T : Rat := 6/5/2^36
def S : Rat := 1/2^50
def beta : Rat := 1 - 1/2^10
def c : Rat := 7/6/2^36
def lam : Rat := 1 - 1/2^51
def lam' : Rat := 1 - 1/2^61
def C1 : Nat := 5
def eps : Rat := 3/16
def delta : Rat := 1/128
def kappa : Rat := 1/2^74
def g1 : Rat := 1 - eps * (1 + c)
def g2 : Rat := eps * c * T
def g3 : Rat := eps * (1 - lam')
def g4 : Rat := T * (1 - eps)
def g5 : Rat := 1/4 - delta - 5 * eps / 4
def g6 : Rat := 1 - delta - eps
def g7 : Rat := eps

/-- All conditions and margins of Set B, and `g2 = (21/80)·2^-72`. -/
theorem certified :
    1 - T < lam ∧ 1 - S < lam ∧ lam < 1 ∧ (1 - T) * (1 + c / beta) < lam ∧ lam < lam' ∧
    (1 - S) + beta * S < lam' ∧ lam' < 1 ∧ eps * C1 < 1 ∧ 0 < delta ∧ delta < 1/8 ∧
    eps < 1/3 ∧ 0 < c ∧ 0 < beta ∧ beta < 1 ∧
    kappa < g1 ∧ kappa < g2 ∧ kappa < g3 ∧ kappa < g4 ∧ kappa < g5 ∧ kappa < g6 ∧
    kappa < g7 ∧
    g2 = 21/80/2^72 := by
  decide +kernel
end SetB

/-! ### Set A: `κ = 2^-76`
(`τ = 1 - T` with `T = 2^-36` as in `tau_A`; `C₁ = 14`.) -/
namespace SetA
def T : Rat := 1/2^36
def S : Rat := 1/2^50
def beta : Rat := 1 - 1/2^10
def c : Rat := 31/32/2^36
def lam : Rat := 1 - 1/2^51
def lam' : Rat := 1 - 1/2^61
def C1 : Nat := 14
def eps : Rat := 1/15
def delta : Rat := 1/16
def kappa : Rat := 1/2^76
def g1 : Rat := 1 - eps * (1 + c)
def g2 : Rat := eps * c * T
def g3 : Rat := eps * (1 - lam')
def g4 : Rat := T * (1 - eps)
def g5 : Rat := 1/4 - delta - 3 * eps / 2
def g6 : Rat := 1 - delta - eps
def g7 : Rat := eps

/-- All conditions and margins of Set A (and, for reference, `g2 = (31/480)·2^-72`).
Set A keeps the paper's `α`, so it records `ε < 1/12`, the condition used in the paper's (40). -/
theorem certified :
    1 - T < lam ∧ 1 - S < lam ∧ lam < 1 ∧ (1 - T) * (1 + c / beta) < lam ∧ lam < lam' ∧
    (1 - S) + beta * S < lam' ∧ lam' < 1 ∧ eps * C1 < 1 ∧ 0 < delta ∧ delta < 1/8 ∧
    eps < 1/12 ∧ 0 < c ∧ 0 < beta ∧ beta < 1 ∧
    kappa < g1 ∧ kappa < g2 ∧ kappa < g3 ∧ kappa < g4 ∧ kappa < g5 ∧ kappa < g6 ∧
    kappa < g7 ∧
    g2 = 31/480/2^72 := by
  decide +kernel
end SetA

/-! ### The paper's parameter set (38), for comparison
Here `g4` and `g5` take the paper's forms; the smallest margin is `g2 = 2^-181`. -/
namespace PaperSet
def T : Rat := 1/2^50
def S : Rat := 1/2^50
def beta : Rat := 1/2
def c : Rat := 1/2^56
def lam : Rat := 1 - 1/2^52
def lam' : Rat := 1 - 1/2^54
def C1 : Nat := 20
def eps : Rat := 1/2^75
def delta : Rat := 1/16
def g1 : Rat := 1 - eps * (1 + c)
def g2 : Rat := eps * c * T
def g3 : Rat := eps * (1 - lam')
def g4 : Rat := 1 - (1 - T) - eps * (2 - (1 - T))
def g5 : Rat := 1/4 - delta - 3 * eps / 2
def g6 : Rat := 1 - delta - eps
def g7 : Rat := eps

/-- All conditions of the paper's set; the margins are positive, and the minimum margin is
`g2 = 2^-181`. -/
theorem certified :
    1 - T < lam ∧ 1 - S < lam ∧ lam < 1 ∧ (1 - T) * (1 + c / beta) < lam ∧ lam < lam' ∧
    (1 - S) + beta * S < lam' ∧ lam' < 1 ∧ eps * C1 < 1 ∧ 0 < delta ∧ delta < 1/8 ∧
    eps < 1/3 ∧ 0 < c ∧ 0 < beta ∧ beta < 1 ∧
    0 < g2 ∧ g2 ≤ g1 ∧ g2 ≤ g3 ∧ g2 ≤ g4 ∧ g2 ≤ g5 ∧ g2 ≤ g6 ∧ g2 ≤ g7 ∧
    g2 = 1/2^181 := by
  decide +kernel
end PaperSet

end IntMulKappa

/-! ## Axiom audit -/

-- Section 1
#print axioms IntMulKappa.printed_values_h100
#print axioms IntMulKappa.counts_h46
#print axioms IntMulKappa.relations_h46
#print axioms IntMulKappa.eta_b_h46
-- Section 2
#print axioms IntMulKappa.ySeq_spec
#print axioms IntMulKappa.rate_cert
#print axioms IntMulKappa.tau_B
#print axioms IntMulKappa.tau_A
#print axioms IntMulKappa.tau_100
#print axioms IntMulKappa.sigma_paper
-- Section 3
#print axioms IntMulKappa.pow_add_le
#print axioms IntMulKappa.sum_pow_le
#print axioms IntMulKappa.depth_unroll
#print axioms IntMulKappa.guard_instances_h100
#print axioms IntMulKappa.depth_unroll_C5
#print axioms IntMulKappa.depth_unroll_C2
-- Section 4
#print axioms IntMulKappa.mem_allV
#print axioms IntMulKappa.tv_add_phi_le
#print axioms IntMulKappa.tv_le_of_checks
#print axioms IntMulKappa.edges_allV_length
#print axioms IntMulKappa.edges_ok_25
#print axioms IntMulKappa.edges_ok_46
#print axioms IntMulKappa.edges_ok_100
#print axioms IntMulKappa.vertices_ok_25
#print axioms IntMulKappa.vertices_ok_46
#print axioms IntMulKappa.vertices_ok_100
#print axioms IntMulKappa.chain_tv_bound
#print axioms IntMulKappa.chain_tv_bound_25
#print axioms IntMulKappa.chain_tv_bound_46
#print axioms IntMulKappa.extremal_tv
-- Section 5
#print axioms IntMulKappa.SetB.certified
#print axioms IntMulKappa.SetA.certified
#print axioms IntMulKappa.PaperSet.certified
