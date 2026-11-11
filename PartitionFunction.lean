import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# The partition function `p(n)`

Generating function, Ramanujan's congruence modulo 5, the Hardy–Ramanujan asymptotic formula and
Rademacher's exact series, organised in four modules.

Every definition is complete (no `sorry` occurs inside a definition) and every reduction between
statements is proved. Each remaining `sorry` closes a *terminal* obligation: either a classical
theorem whose proof needs theory that Mathlib does not yet contain, or a self-contained analytic
lemma whose proof is routine but long. No terminal obligation is used to prove another one.

## Verification status

Checked with Lean 4 (`leanprover/lean4:v4.36.0-rc2`) against Mathlib `master` at commit
`3881f16c6c9b` (10 November 2026), by `lake env lean PartitionFunction.lean` in a Mathlib
checkout: the file compiles without errors, and the only warnings are
`declaration uses 'sorry'` for the ten terminal obligations

* Module 1: `hasSum_partitionFunction_mul_pow`;
* Module 2: `qPochhammerInfinite_pow_three`, `ramanujan_identity_five`;
* Module 3: `hardy_ramanujan_asymptotic`, `partitionFunction_eq_circleIntegral`,
  `partitionGenFun_asymptotic_near_one`;
* Module 4: `eta_modular_transformation`, `abs_rademacherTerm_le`, `tsum_rademacherTerm`,
  `rademacherTerm_one_isEquivalent`.

As reported by `#print axioms` and `#print sorries`: `partition_generating_function` is fully
proved (it depends only on `propext`, `Classical.choice` and `Quot.sound`);
`ramanujan_congruence_5` depends only on `qPochhammerInfinite_pow_three` (Jacobi's identity);
`hardy_ramanujan_asymptotic` is itself terminal; and `rademacher_exact_series` depends only on
`abs_rademacherTerm_le` and `tsum_rademacherTerm`. All terminal obligations are classical
statements; apart from the two standard analytic facts `hasSum_partitionFunction_mul_pow` and
`partitionFunction_eq_circleIntegral`, the underlying formulas were also tested numerically
before being stated (this is evidence, not proof).

## Deviations from the requested specification

1. *Imports.* Three of the requested modules do not exist in current Mathlib:
   `Mathlib.Data.Nat.Partitions`, `Mathlib.Analysis.SpecialFunctions.Trigonometric.Hyperbolic`
   and `Mathlib.Analysis.Asymptotics.Asymptotics`. They are replaced by
   `Mathlib.Combinatorics.Enumerative.Partition.Basic`,
   `Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp` and
   `Mathlib.Analysis.Asymptotics.AsymptoticEquivalent`. Further imports are needed for the
   statements.
2. *Saddle point (Module 3).* The request places the saddle point at
   $q = \exp(-\pi\sqrt{2/(3n)})$. The correct location is $q = \exp(-\pi/\sqrt{6n})$, whose
   exponent is half of the requested one; see `saddle_point_value` and `saddle_point_minimal`,
   which are proved.
3. *Real-valued $A_k(n)$ (Module 4).* `rademacherSum` has the requested type `ℕ → ℕ → ℝ`. It is
   the real part of the complex exponential sum `rademacherSumComplex`, whose imaginary part is
   proved to vanish (`rademacherSumComplex_im`).
4. *Generality.* `partition_generating_function` is stated over an arbitrary field `K`, with
   `ℝ` and `ℂ` as corollaries; $1/(q; q)_\infty$ is written with `⁻¹` in `K⟦X⟧`.
5. *Namespace.* All declarations live in the namespace `PartitionTheory`.

## References

* [HR] G. H. Hardy, S. Ramanujan, *Asymptotic formulae in combinatory analysis*,
  Proc. London Math. Soc. (2) 17 (1918), 75–115.
* [Ram] S. Ramanujan, *Some properties of `p(n)`, the number of partitions of `n`*,
  Proc. Cambridge Philos. Soc. 19 (1919), 207–210.
* [Rad] H. Rademacher, *On the partition function `p(n)`*,
  Proc. London Math. Soc. (2) 43 (1937), 241–254.
* [Leh] D. H. Lehmer, *On the series for the partition function*,
  Trans. Amer. Math. Soc. 43 (1938), 271–295.
* [Apo] T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed.,
  Springer GTM 41, Chapters 3 and 5.
* [And] G. E. Andrews, *The Theory of Partitions*, Cambridge University Press, Chapters 1, 5, 10.
-/

noncomputable section

open PowerSeries Filter Asymptotics
open scoped Real Topology PowerSeries.WithPiTopology

namespace PartitionTheory

/-!
## MODULE 1: Definitions and the generating function

Main result: `partition_generating_function`, i.e.
$\sum_{n \ge 0} p(n) X^n = 1 / (X; X)_\infty$ in $K[[X]]$ for every field $K$ (in particular
$K = \mathbb{R}, \mathbb{C}$). The inverse-free form
$\bigl(\sum_n p(n) X^n\bigr) (X; X)_\infty = 1$ holds over every commutative ring
(`partitionGenFun_mul_qPochhammerInfinite`). Both are proved here without `sorry`.

### Proof strategy

* **Combinatorial bijection (Euler).** A partition of $n$ is a finitely supported multiplicity
  function $(m_i)_{i \ge 1}$ with $\sum_i i\,m_i = n$. Hence the coefficient of $X^n$ in
  $\prod_{i \ge 1} \sum_{j \ge 0} X^{ij}$ is $p(n)$; the product converges $X$-adically because
  its $i$-th factor is $\equiv 1 \pmod{X^i}$. Mathlib provides this as
  `Nat.Partition.hasProd_genFun` (bijection `Nat.Partition.toFinsuppAntidiag`). Each factor is a
  geometric series, $(1 - X^i) \sum_j X^{ij} = 1$, and multiplying the two convergent products
  factor by factor gives the identity.
* **Euler's pentagonal number theorem.**
  $(X; X)_\infty = \sum_{k \in \mathbb{Z}} (-1)^k X^{k(3k-1)/2}$; see
  `qPochhammerInfinite_eq_pentagonalSeries`, which rests on Mathlib's
  `PowerSeries.WithPiTopology.tprod_one_sub_X_pow`. Together with the generating function it
  yields Euler's recurrence $\sum_{k \in \mathbb{Z}} (-1)^k p(n - k(3k-1)/2) = \delta_{n,0}$
  (`partitionGenFun_mul_pentagonalSeries`).
* **Jacobi's triple product** (not yet in Mathlib).
  $\prod_{n \ge 1} (1 - x^{2n})(1 + x^{2n-1} z)(1 + x^{2n-1} z^{-1})
  = \sum_{m \in \mathbb{Z}} x^{m^2} z^m$.
  The substitution $x = q^{3/2}$, $z = -q^{1/2}$ gives the pentagonal number theorem. In the
  equivalent form $\prod_{n \ge 1} (1 - q^n)(1 - z q^n)(1 - z^{-1} q^{n-1})
  = \sum_{m \in \mathbb{Z}} (-1)^m z^m q^{m(m+1)/2}$, dividing by $1 - z^{-1}$ and letting
  $z \to 1$ gives Jacobi's identity for $(q; q)_\infty^3$, which is used in Module 2.
-/

section GeneratingFunction

/-- The partition function $p(n)$: the number of ways of writing `n` as a sum of positive
integers, the order of the summands being irrelevant. Formally, the cardinality of
`Nat.Partition n` (multisets of positive integers with sum `n`). In particular $p(0) = 1$. -/
def partitionFunction (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

theorem partitionFunction_zero : partitionFunction 0 = 1 := Fintype.card_unique

theorem partitionFunction_one : partitionFunction 1 = 1 := Fintype.card_unique

theorem partitionFunction_pos (n : ℕ) : 0 < partitionFunction n :=
  Fintype.card_pos_iff.mpr ⟨Nat.Partition.indiscrete n⟩

/-- The infinite $q$-Pochhammer symbol $(X; X)_\infty = \prod_{i \ge 1} (1 - X^i)$ (Euler's
function) as a formal power series over a commutative ring `R`.

The infinite product is taken in the $X$-adic topology of `R⟦X⟧`, i.e. the topology of
coefficientwise convergence with `R` discrete. This choice is internal to the definition:
`hasProd_qPochhammerInfinite` shows that the product converges to the same series for every
topology on `R`. -/
def qPochhammerInfinite (R : Type*) [CommRing R] : R⟦X⟧ :=
  letI : TopologicalSpace R := ⊥
  ∏' i : ℕ, ((1 : R⟦X⟧) - X ^ (i + 1))

/-- **Euler's pentagonal number theorem**:
$(X; X)_\infty = \sum_{k \in \mathbb{Z}} (-1)^k X^{k(3k-1)/2}$. -/
theorem qPochhammerInfinite_eq_pentagonalSeries (R : Type*) [CommRing R] :
    qPochhammerInfinite R = PowerSeries.pentagonalSeries R := by
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := ⟨rfl⟩
  exact PowerSeries.WithPiTopology.tprod_one_sub_X_pow R

/-- For every topology on `R`, the partial products of $\prod_{i \ge 1} (1 - X^i)$ converge
coefficientwise to `qPochhammerInfinite R`. -/
theorem hasProd_qPochhammerInfinite (R : Type*) [CommRing R] [TopologicalSpace R] :
    HasProd (fun i : ℕ => (1 : R⟦X⟧) - X ^ (i + 1)) (qPochhammerInfinite R) := by
  rw [qPochhammerInfinite_eq_pentagonalSeries]
  exact PowerSeries.WithPiTopology.hasProd_one_sub_X_pow R

theorem constantCoeff_qPochhammerInfinite (R : Type*) [CommRing R] :
    constantCoeff (qPochhammerInfinite R) = 1 := by
  have h := PowerSeries.coeff_pentagonalSeries_pentagonal R 0
  rw [show pentagonal 0 = 0 from rfl] at h
  rw [qPochhammerInfinite_eq_pentagonalSeries, ← coeff_zero_eq_constantCoeff_apply]
  simpa using h

/-- The generating function $\sum_{n \ge 0} p(n) X^n \in R[[X]]$ of the partition function. -/
def partitionGenFun (R : Type*) [CommSemiring R] : R⟦X⟧ :=
  PowerSeries.mk fun n => (partitionFunction n : R)

@[simp]
theorem coeff_partitionGenFun (R : Type*) [CommSemiring R] (n : ℕ) :
    coeff n (partitionGenFun R) = (partitionFunction n : R) :=
  coeff_mk _ _

/-- Euler's product in its combinatorial form:
$\sum_n p(n) X^n = \prod_{i \ge 1} \sum_{j \ge 0} X^{ij}$. -/
theorem hasProd_partitionGenFun (R : Type*) [CommSemiring R] [TopologicalSpace R] [T2Space R]
    [IsTopologicalSemiring R] :
    HasProd (fun i : ℕ => ∑' j : ℕ, (X : R⟦X⟧) ^ ((i + 1) * j)) (partitionGenFun R) := by
  have h := Nat.Partition.hasProd_powerSeriesMk_card_restricted R (fun _ => True)
  simpa [partitionGenFun, partitionFunction, Nat.Partition.restricted] using h

/-- **Euler's generating function identity**, inverse-free form, over any commutative ring:
$\bigl(\sum_{n \ge 0} p(n) X^n\bigr) \cdot \prod_{i \ge 1} (1 - X^i) = 1$. -/
theorem partitionGenFun_mul_qPochhammerInfinite (R : Type*) [CommRing R] :
    partitionGenFun R * qPochhammerInfinite R = 1 := by
  -- Work in the `X`-adic topology (`R` discrete) and multiply the two products factor by factor.
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := ⟨rfl⟩
  have h := (hasProd_partitionGenFun R).mul (hasProd_qPochhammerInfinite R)
  -- Each factor is a geometric series: `(∑ j, (X ^ (i + 1)) ^ j) * (1 - X ^ (i + 1)) = 1`.
  have h1 : (fun i : ℕ => (∑' j : ℕ, (X : R⟦X⟧) ^ ((i + 1) * j)) * (1 - X ^ (i + 1))) =
      fun _ => 1 := by
    funext i
    simp_rw [pow_mul]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  rw [h1] at h
  exact h.unique hasProd_one

/-- **Generating function of the partition function** (Euler):
$\sum_{n \ge 0} p(n) X^n = \dfrac{1}{(X; X)_\infty}$ as formal power series over a field `K`.
The inverse exists because $(X; X)_\infty$ has constant coefficient $1$. -/
theorem partition_generating_function (K : Type*) [Field K] :
    partitionGenFun K = (qPochhammerInfinite K)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · exact partitionGenFun_mul_qPochhammerInfinite K
  · simp [constantCoeff_qPochhammerInfinite]

/-- The generating function identity over $\mathbb{R}$. -/
theorem partition_generating_function_real :
    partitionGenFun ℝ = (qPochhammerInfinite ℝ)⁻¹ :=
  partition_generating_function ℝ

/-- The generating function identity over $\mathbb{C}$. -/
theorem partition_generating_function_complex :
    partitionGenFun ℂ = (qPochhammerInfinite ℂ)⁻¹ :=
  partition_generating_function ℂ

/-- **Euler's recurrence** in generating-function form:
$\bigl(\sum_n p(n) X^n\bigr) \cdot \sum_{k \in \mathbb{Z}} (-1)^k X^{k(3k-1)/2} = 1$. -/
theorem partitionGenFun_mul_pentagonalSeries (R : Type*) [CommRing R] :
    partitionGenFun R * PowerSeries.pentagonalSeries R = 1 := by
  rw [← qPochhammerInfinite_eq_pentagonalSeries, partitionGenFun_mul_qPochhammerInfinite]

/-- **Analytic form of the generating function.** For $|q| < 1$ the series $\sum_n p(n) q^n$
converges absolutely and equals $1 / \phi(q)$, where $\phi(q) = \prod_{n \ge 1} (1 - q^n)$ is
Mathlib's `eulerFunction` (cf. `eulerFunction_eq_tprod`).

Proof sketch: for $0 \le r < 1$ the partial sums of $\sum_n p(n) r^n$ are bounded by
$\prod_{i \ge 1} (1 - r^i)^{-1} \le \exp\bigl(\sum_i r^i / (1 - r^i)\bigr) < \infty$, which gives
absolute convergence; the value is then identified by evaluating the formal identity
`partitionGenFun_mul_qPochhammerInfinite` at `q` (Cauchy product of absolutely convergent
series, with `hasSum_eulerFunction_pentagonalSeries` for the second factor). -/
theorem hasSum_partitionFunction_mul_pow {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partitionFunction n : ℂ) * q ^ n) (eulerFunction q)⁻¹ := by
  sorry

end GeneratingFunction

/-!
## MODULE 2: Ramanujan's congruence modulo 5

Main result: `ramanujan_congruence_5`, i.e. $p(5n + 4) \equiv 0 \pmod 5$. Following Ramanujan's
elementary argument [Ram], it is *proved* here from a single terminal obligation, Jacobi's
identity for $(X; X)_\infty^3$ (`qPochhammerInfinite_pow_three`).

### Elementary route (Jacobi triple product and pentagonal number theorem)

Write $E = (X; X)_\infty \in \mathbb{F}_5[[X]]$ and $P = \sum_n p(n) X^n$, so $P E = 1$.

1. *Frobenius.* $E^5 = E(X^5)$ in characteristic $5$ (`pow_five_eq_expand`, proved). Hence
   $P = E^4 \cdot P(X^5)$ (`partitionGenFun_zmod_five_eq`, proved).
2. *Jacobi's identity.* $E^3 = \sum_{k \ge 0} (-1)^k (2k+1) X^{k(k+1)/2}$
   (`qPochhammerInfinite_pow_three`, terminal).
3. *The congruence emerges here.* By 2 and the pentagonal number theorem,
   $E^4 = E \cdot E^3 = \sum_{m \in \mathbb{Z}} \sum_{k \ge 0} (-1)^{m+k} (2k+1)
   X^{m(3m-1)/2 + k(k+1)/2}$. If the exponent $N$ satisfies $N \equiv 4 \pmod 5$, then
   $(6m-1)^2 + 3(2k+1)^2 = 24N + 4 \equiv 0 \pmod 5$. Since $-3$ is a quadratic non-residue
   modulo $5$, this forces $2k + 1 \equiv 0 \pmod 5$, so the coefficient vanishes in
   $\mathbb{F}_5$ (`coeff_qPochhammerInfinite_pow_four`, proved from 2).
4. *Conclusion.* In $P = E^4 \cdot P(X^5)$ the second factor only involves exponents divisible
   by $5$, so the coefficient of $X^{5n+4}$ in $P$ is a combination of coefficients of
   $X^{5n'+4}$ in $E^4$, which vanish (`coeff_partitionGenFun_zmod_five`, proved).

### Modular route (Dedekind eta function)

With $q = e^{2\pi i \tau}$, $\operatorname{Im} \tau > 0$, the generating function is
$\sum_n p(n) q^n = q^{1/24} / \eta(\tau)$ (`hasSum_partitionFunction_qParam`), where
$\eta(\tau) = q^{1/24} \prod_{n \ge 1} (1 - q^n)$ is Mathlib's `ModularForm.eta`. Under modular
substitutions, $\eta(\tau + 1) = e^{\pi i / 12} \eta(\tau)$ and
$\eta(-1/\tau) = \sqrt{-i\tau}\, \eta(\tau)$ (`eta_S_transform` in Module 3): $\eta$ is a modular
form of weight $1/2$ on $\mathrm{SL}_2(\mathbb{Z})$ with a multiplier system given by Dedekind
sums (`eta_modular_transformation` in Module 4). Consequently the eta quotient
$f(\tau) = \eta(5\tau)^5 / \eta(\tau) = q\,(q^5; q^5)_\infty^5 \sum_n p(n) q^n$ is a modular form
of weight $2$ on $\Gamma_0(5)$ with character $\bigl(\tfrac{\cdot}{5}\bigr)$. The operator
$U_5 : \sum a_n q^n \mapsto \sum a_{5n} q^n$ preserves this two-dimensional space and its
one-dimensional subspace of forms vanishing at $\infty$, which is spanned by $f$; comparing the
coefficients of $q$ gives $U_5 f = p(4) f = 5 f$. Since
$U_5 f = (q; q)_\infty^5 \sum_{m \ge 1} p(5m - 1) q^m$, this is Ramanujan's identity
$\sum_{n \ge 0} p(5n+4) q^n = 5\, (q^5; q^5)_\infty^5 / (q; q)_\infty^6$
(`ramanujan_identity_five`, terminal), in which the congruence is visible as the factor $5$.
Prerequisites missing from Mathlib: modularity of eta quotients, the operators $U_p$, and the
dimension of $M_2(\Gamma_0(5), \chi)$.
-/

section RamanujanCongruence

/-- **Frobenius.** In characteristic $5$, $f(X)^5 = f(X^5)$ for every $f \in \mathbb{F}_5[[X]]$.
`PowerSeries.expand 5 _ f` is the substitution $X \mapsto X^5$. -/
theorem pow_five_eq_expand (f : (ZMod 5)⟦X⟧) :
    f ^ 5 = PowerSeries.expand 5 (by norm_num) f := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := PowerSeries.map_frobenius_expand (p := 5) (hp := by norm_num) (f := f)
  rw [ZMod.frobenius_zmod] at h
  simpa using h.symm

/-- The series $\sum_{k \ge 0} (-1)^k (2k+1) X^{k(k+1)/2}$. The coefficient of $X^n$ is written
as a finite sum over $k \le n$ with at most one non-zero term, since $k \le k(k+1)/2$. -/
def jacobiCubeSeries (R : Type*) [CommRing R] : R⟦X⟧ :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1),
    if k * (k + 1) / 2 = n then (-1) ^ k * (2 * (k : R) + 1) else 0

/-- **Jacobi's identity**: $(X; X)_\infty^3 = \sum_{k \ge 0} (-1)^k (2k+1) X^{k(k+1)/2}$.

Terminal obligation. It follows from Jacobi's triple product (see the Module 1 outline), which
is not yet in Mathlib; an alternative is a direct proof by a sign-reversing involution. -/
theorem qPochhammerInfinite_pow_three (R : Type*) [CommRing R] :
    qPochhammerInfinite R ^ 3 = jacobiCubeSeries R := by
  sorry

/-- The arithmetic core of Ramanujan's argument: if
$\tfrac{m(3m-1)}{2} + \tfrac{k(k+1)}{2} = 5n + 4$ then $2k + 1 \equiv 0 \pmod 5$.

Indeed $(6m-1)^2 + 3(2k+1)^2 = 24(5n+4) + 4 \equiv 0 \pmod 5$, and $-3$ is a quadratic
non-residue modulo $5$. -/
theorem two_mul_add_one_eq_zero_of_pentagonal_add_triangular (m : ℤ) (k n : ℕ)
    (h : pentagonal m + k * (k + 1) / 2 = 5 * n + 4) : 2 * (k : ZMod 5) + 1 = 0 := by
  have h1 : 2 * (pentagonal m : ℤ) = m * (3 * m - 1) := two_mul_natCast_pentagonal m
  have h2 : (2 : ℤ) * ((k * (k + 1) / 2 : ℕ) : ℤ) = k * (k + 1) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd
  have h3 : ((pentagonal m : ℕ) : ℤ) + ((k * (k + 1) / 2 : ℕ) : ℤ) = 5 * n + 4 := by
    exact_mod_cast h
  have h4 : (6 * m - 1) ^ 2 + 3 * (2 * (k : ℤ) + 1) ^ 2 = 5 * (24 * n + 20) := by
    linear_combination (-12) * h1 - 12 * h2 + 24 * h3
  have h5 := congrArg (Int.cast : ℤ → ZMod 5) h4
  push_cast at h5
  have key : ∀ x y : ZMod 5, x ^ 2 + 3 * y ^ 2 = 0 → y = 0 := by decide
  exact key _ _ (h5.trans (by rw [show (5 : ZMod 5) = 0 by decide, zero_mul]))

/-- The coefficients of $X^{5n+4}$ in $(X; X)_\infty^4$ vanish modulo $5$.

Proved from Jacobi's identity `qPochhammerInfinite_pow_three` and the pentagonal number theorem:
this is step 3 of the elementary route in the module docstring. -/
theorem coeff_qPochhammerInfinite_pow_four (n : ℕ) :
    coeff (5 * n + 4) (qPochhammerInfinite (ZMod 5) ^ 4) = 0 := by
  have hE4 : qPochhammerInfinite (ZMod 5) ^ 4 =
      PowerSeries.pentagonalSeries (ZMod 5) * jacobiCubeSeries (ZMod 5) := by
    rw [← qPochhammerInfinite_pow_three, ← qPochhammerInfinite_eq_pentagonalSeries]
    ring
  rw [hE4, coeff_mul]
  refine Finset.sum_eq_zero ?_
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  dsimp only at hij ⊢
  by_cases hi : i ∈ Set.range pentagonal
  · -- `i` is a pentagonal number: every term of the coefficient of `X ^ j` in `E ^ 3` vanishes.
    obtain ⟨m, rfl⟩ := hi
    have hj : coeff j (jacobiCubeSeries (ZMod 5)) = 0 := by
      rw [jacobiCubeSeries, coeff_mk]
      refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs with hk
      · rw [two_mul_add_one_eq_zero_of_pentagonal_add_triangular m k n (by rw [hk]; exact hij),
          mul_zero]
      · rfl
    rw [hj, mul_zero]
  · -- `i` is not a pentagonal number: the coefficient of `X ^ i` in `E` vanishes.
    rw [PowerSeries.coeff_pentagonalSeries_eq_zero _ hi, zero_mul]

/-- Over $\mathbb{F}_5$: $P(X) = (X; X)_\infty^4 \cdot P(X^5)$, where $P = \sum_n p(n) X^n$. -/
theorem partitionGenFun_zmod_five_eq :
    partitionGenFun (ZMod 5) = qPochhammerInfinite (ZMod 5) ^ 4 *
      PowerSeries.expand 5 (by norm_num) (partitionGenFun (ZMod 5)) := by
  have hPE : partitionGenFun (ZMod 5) * qPochhammerInfinite (ZMod 5) = 1 :=
    partitionGenFun_mul_qPochhammerInfinite _
  have h5 : PowerSeries.expand 5 (by norm_num) (partitionGenFun (ZMod 5)) *
      qPochhammerInfinite (ZMod 5) ^ 5 = 1 := by
    rw [pow_five_eq_expand, ← map_mul, hPE, map_one]
  calc partitionGenFun (ZMod 5)
      = partitionGenFun (ZMod 5) * (PowerSeries.expand 5 (by norm_num) (partitionGenFun (ZMod 5)) *
          qPochhammerInfinite (ZMod 5) ^ 5) := by rw [h5, mul_one]
    _ = qPochhammerInfinite (ZMod 5) ^ 4 *
          PowerSeries.expand 5 (by norm_num) (partitionGenFun (ZMod 5)) *
          (partitionGenFun (ZMod 5) * qPochhammerInfinite (ZMod 5)) := by ring
    _ = qPochhammerInfinite (ZMod 5) ^ 4 *
          PowerSeries.expand 5 (by norm_num) (partitionGenFun (ZMod 5)) := by rw [hPE, mul_one]

/-- The coefficient of $X^{5n+4}$ in $\sum_n p(n) X^n$ vanishes in $\mathbb{F}_5$. -/
theorem coeff_partitionGenFun_zmod_five (n : ℕ) :
    coeff (5 * n + 4) (partitionGenFun (ZMod 5)) = 0 := by
  rw [partitionGenFun_zmod_five_eq, coeff_mul]
  refine Finset.sum_eq_zero ?_
  rintro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  dsimp only at hij ⊢
  by_cases hj : 5 ∣ j
  · -- `j = 5 m`, hence `i = 5 (n - m) + 4` and the coefficient of `E ^ 4` vanishes.
    obtain ⟨m, rfl⟩ := hj
    have hi : i = 5 * (n - m) + 4 := by omega
    rw [hi, coeff_qPochhammerInfinite_pow_four, zero_mul]
  · -- `P(X ^ 5)` has no term of exponent `j` when `5 ∤ j`.
    rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hj, mul_zero]

/-- **Ramanujan's congruence modulo 5**: $p(5n + 4) \equiv 0 \pmod 5$ for every $n \ge 0$. -/
theorem ramanujan_congruence_5 (n : ℕ) : partitionFunction (5 * n + 4) ≡ 0 [MOD 5] := by
  have h := coeff_partitionGenFun_zmod_five n
  rw [coeff_partitionGenFun] at h
  exact Nat.modEq_zero_iff_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp h)

/-- **Ramanujan's identity**
$\sum_{n \ge 0} p(5n+4) X^n = 5\, \dfrac{(X^5; X^5)_\infty^5}{(X; X)_\infty^6}$, stated without
denominators in $\mathbb{Z}[[X]]$.

Terminal obligation; it is the outcome of the modular route in the module docstring
($U_5 f = 5 f$ for $f = \eta(5\tau)^5 / \eta(\tau)$) and gives a second proof of
`ramanujan_congruence_5`. -/
theorem ramanujan_identity_five :
    (PowerSeries.mk fun n => (partitionFunction (5 * n + 4) : ℤ)) * qPochhammerInfinite ℤ ^ 6 =
      5 * PowerSeries.expand 5 (by norm_num) (qPochhammerInfinite ℤ) ^ 5 := by
  sorry

/-- The Dedekind eta function in terms of Euler's function:
$\eta(\tau) = q^{1/24} \phi(q)$ with $q = e^{2\pi i \tau}$, for $\operatorname{Im} \tau > 0$.
Here `Function.Periodic.qParam h τ` is $e^{2\pi i \tau / h}$. -/
theorem eta_eq_qParam_mul_eulerFunction {τ : ℂ} (hτ : 0 < τ.im) :
    ModularForm.eta τ =
      Function.Periodic.qParam 24 τ * eulerFunction (Function.Periodic.qParam 1 τ) := by
  rw [eulerFunction_eq_tprod (Function.Periodic.norm_qParam_lt_one one_pos hτ)]
  rfl

/-- The partition generating function as a modular object:
$\sum_{n \ge 0} p(n) q^n = q^{1/24} / \eta(\tau)$ for $q = e^{2\pi i \tau}$,
$\operatorname{Im} \tau > 0$. Proved from `hasSum_partitionFunction_mul_pow`. -/
theorem hasSum_partitionFunction_qParam {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => (partitionFunction n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 24 τ / ModularForm.eta τ) := by
  have h := hasSum_partitionFunction_mul_pow (Function.Periodic.norm_qParam_lt_one one_pos hτ)
  have h24 : Function.Periodic.qParam 24 τ ≠ 0 := Function.Periodic.qParam_ne_zero τ
  rwa [eta_eq_qParam_mul_eulerFunction hτ, ← div_div, div_self h24, one_div]

end RamanujanCongruence

/-!
## MODULE 3: The Hardy–Ramanujan asymptotic formula

Main result: `hardy_ramanujan_asymptotic`, i.e.
$p(n) \sim \dfrac{1}{4 n \sqrt 3} \exp\Bigl(\pi \sqrt{\tfrac{2n}{3}}\Bigr)$ as $n \to \infty$
[HR], stated with `Asymptotics.IsEquivalent` along `Filter.atTop`.

### Proof strategy (circle method)

1. *Cauchy's formula.* $P(q) = \sum_n p(n) q^n = 1/\phi(q)$ is holomorphic in the unit disc and
   $p(n) = \dfrac{1}{2\pi i} \oint_{|q| = r} \dfrac{P(q)}{q^{n+1}}\, dq$ for $0 < r < 1$
   (`partitionFunction_eq_circleIntegral`).
2. *Modular transformation of $\eta$.* Since $P(q) = q^{1/24} / \eta(\tau)$, the relation
   $\eta(-1/\tau) = \sqrt{-i\tau}\, \eta(\tau)$ (`eta_S_transform`, available in Mathlib) gives
   the exact functional equation
   $P(e^{-t}) = \sqrt{\tfrac{t}{2\pi}} \exp\Bigl(\tfrac{\pi^2}{6t} - \tfrac{t}{24}\Bigr)
   P(e^{-4\pi^2/t})$ for $\operatorname{Re} t > 0$, hence
   $P(e^{-t}) \sim \sqrt{t / 2\pi}\, e^{\pi^2 / 6t}$ as $t \to 0^+$
   (`partitionGenFun_asymptotic_near_one`). The singularity at $q = 1$ is the dominant one; at a
   primitive $k$-th root of unity the growth is only $\exp\bigl(\pi^2 / (6 k^2 t)\bigr)$.
3. *Saddle point.* On the positive real axis the integrand has size
   $\exp\bigl(\pi^2/(6t) + nt\bigr)$ at $q = e^{-t}$. This is minimal at $t_0 = \pi / \sqrt{6n}$,
   with minimal value $\exp\bigl(\pi \sqrt{2n/3}\bigr)$ (`saddle_point_value`,
   `saddle_point_minimal`, both proved). The contour is therefore the circle of radius
   $r = e^{-\pi/\sqrt{6n}}$, and the saddle point is $q = e^{-\pi/\sqrt{6n}}$.
4. *Major arc.* On a short arc around $q = 1$ one replaces $P$ by
   $\sqrt{t/2\pi}\, e^{\pi^2/6t - t/24}$; the resulting integral is evaluated exactly and equals
   $\dfrac{1}{2\pi\sqrt 2} \dfrac{d}{dn} \dfrac{e^{K \lambda_n}}{\lambda_n}$ up to an exponentially
   smaller error, where $K = \pi\sqrt{2/3}$ and $\lambda_n = \sqrt{n - 1/24}$. This is
   asymptotic to $e^{K\sqrt n} / (4 n \sqrt 3)$.
5. *Minor arcs.* On the rest of the circle the integrand is $O\bigl(\exp(c K \sqrt n)\bigr)$ for
   a constant $c < 1$ (the largest contribution comes from $q = -1$, where step 2 gives
   $c = 5/8 + \varepsilon$); this is negligible against the main term.

Alternatively the theorem follows from Rademacher's series (Module 4): the term $k = 1$ is
asymptotic to the main term (`rademacherTerm_one_isEquivalent`) and the remaining terms are
$O\bigl(e^{K\sqrt n / 2}\bigr)$.
-/

section HardyRamanujan

/-- The Hardy–Ramanujan main term $\dfrac{1}{4 n \sqrt 3} \exp\bigl(\pi \sqrt{2n/3}\bigr)$. -/
def hardyRamanujanMainTerm (n : ℕ) : ℝ :=
  1 / (4 * (n : ℝ) * √3) * Real.exp (π * √(2 * (n : ℝ) / 3))

/-- **Hardy–Ramanujan asymptotic formula** [HR]:
$p(n) \sim \dfrac{1}{4 n \sqrt 3} \exp\Bigl(\pi \sqrt{\tfrac{2n}{3}}\Bigr)$ as $n \to \infty$.

`u ~[atTop] v` unfolds to `(u - v) =o[atTop] v`; see `hardy_ramanujan_tendsto` for the
formulation as a limit of the quotient. Terminal obligation; see the module docstring for the
circle-method proof. -/
theorem hardy_ramanujan_asymptotic :
    (fun n : ℕ => (partitionFunction n : ℝ)) ~[atTop]
      (fun n : ℕ => 1 / (4 * (n : ℝ) * √3) * Real.exp (π * √(2 * (n : ℝ) / 3))) := by
  sorry

/-- The Hardy–Ramanujan formula as a limit: $p(n)$ divided by the main term tends to $1$. -/
theorem hardy_ramanujan_tendsto :
    Tendsto (fun n : ℕ => (partitionFunction n : ℝ) / hardyRamanujanMainTerm n) atTop (𝓝 1) := by
  have hne : ∀ᶠ n : ℕ in atTop, hardyRamanujanMainTerm n ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    unfold hardyRamanujanMainTerm
    positivity
  exact (isEquivalent_iff_tendsto_one hne).mp hardy_ramanujan_asymptotic

/-- **Transformation of $\eta$ under $\tau \mapsto -1/\tau$** (from Mathlib):
$\eta(-1/\tau) = (\sqrt{i})^{-1} \sqrt{\tau}\, \eta(\tau)$ for $\operatorname{Im} \tau > 0$, with
principal square roots; the factor equals $\sqrt{-i\tau}$. -/
theorem eta_S_transform {τ : ℂ} (hτ : 0 < τ.im) :
    ModularForm.eta (-1 / τ) =
      (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt τ * ModularForm.eta τ) := by
  simpa using ModularForm.eta_comp_eq_csqrt_I_inv hτ

/-- **Cauchy's coefficient formula** for the partition function:
$p(n) = \dfrac{1}{2\pi i} \oint_{|z| = r} \dfrac{dz}{\phi(z)\, z^{n+1}}$ for $0 < r < 1$.

Terminal obligation: Cauchy's formula applied to `hasSum_partitionFunction_mul_pow`. -/
theorem partitionFunction_eq_circleIntegral (n : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (partitionFunction n : ℂ) =
      (2 * π * Complex.I)⁻¹ * ∮ z in C(0, r), (eulerFunction z)⁻¹ / z ^ (n + 1) := by
  sorry

/-- **Behaviour of the generating function at the dominant singularity $q = 1$**:
$\sum_n p(n) e^{-nt} \sim \sqrt{\dfrac{t}{2\pi}} \exp\Bigl(\dfrac{\pi^2}{6t}\Bigr)$ as
$t \to 0^+$.

Terminal obligation: combine `hasSum_partitionFunction_qParam` at $\tau = it/2\pi$ with
`eta_S_transform` (step 2 of the module docstring). -/
theorem partitionGenFun_asymptotic_near_one :
    (fun t : ℝ => ∑' n : ℕ, (partitionFunction n : ℝ) * Real.exp (-(n : ℝ) * t)) ~[𝓝[>] 0]
      (fun t : ℝ => √(t / (2 * π)) * Real.exp (π ^ 2 / (6 * t))) := by
  sorry

/-- **Value at the saddle point.** At $t_0 = \pi / \sqrt{6n}$ the exponent
$\pi^2 / (6t) + n t$ takes the value $\pi \sqrt{2n/3}$, the exponent of the Hardy–Ramanujan
formula. -/
theorem saddle_point_value (n : ℕ) (hn : 0 < n) :
    π ^ 2 / (6 * (π / √(6 * (n : ℝ)))) + n * (π / √(6 * (n : ℝ))) = π * √(2 * (n : ℝ) / 3) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (0 : ℝ) < √(6 * (n : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hsq : √(6 * (n : ℝ)) ^ 2 = 6 * n := Real.sq_sqrt (by positivity)
  have h3 : √(2 * (n : ℝ) / 3) = √(6 * (n : ℝ)) / 3 := by
    rw [show 2 * (n : ℝ) / 3 = (√(6 * (n : ℝ)) / 3) ^ 2 by rw [div_pow, hsq]; ring]
    exact Real.sqrt_sq (by positivity)
  have hn6 : (n : ℝ) = √(6 * (n : ℝ)) ^ 2 / 6 := by rw [hsq]; ring
  have hs' : √(6 * (n : ℝ)) ≠ 0 := hs.ne'
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [h3]
  generalize √(6 * (n : ℝ)) = s at hn6 hs' ⊢
  rw [hn6]
  field_simp
  ring

/-- **Minimality at the saddle point.** For every $t > 0$,
$\pi \sqrt{2n/3} \le \pi^2 / (6t) + n t$ (inequality of arithmetic and geometric means). Together
with `saddle_point_value`, this locates the saddle point of the Cauchy integrand on the real
axis at $q = e^{-t_0}$, $t_0 = \pi / \sqrt{6n}$. -/
theorem saddle_point_minimal (n : ℕ) {t : ℝ} (ht : 0 < t) :
    π * √(2 * (n : ℝ) / 3) ≤ π ^ 2 / (6 * t) + n * t := by
  have ht' : t ≠ 0 := ht.ne'
  have hsq : (π * √(2 * (n : ℝ) / 3)) ^ 2 = 4 * (π ^ 2 / (6 * t)) * (n * t) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [hsq]
  nlinarith [sq_nonneg (π ^ 2 / (6 * t) - n * t)]

end HardyRamanujan

/-!
## MODULE 4: Rademacher's exact series

Main result: `rademacher_exact_series` [Rad], i.e. for $n \ge 1$
$$p(n) = \frac{1}{\pi\sqrt 2} \sum_{k=1}^{\infty} A_k(n)\, \sqrt k\,
  \frac{d}{dn}\left( \frac{\sinh\bigl(\frac{\pi}{k} \sqrt{\frac23 (n - \frac1{24})}\bigr)}
  {\sqrt{n - \frac1{24}}} \right),
\qquad A_k(n) = \sum_{\substack{0 \le h < k \\ \gcd(h,k) = 1}} \omega_{h,k}\, e^{-2\pi i n h / k},$$
where $\omega_{h,k} = e^{\pi i s(h,k)}$ and $s(h,k)$ is the Dedekind sum. Equivalently, in terms
of the modified Bessel function $I_{3/2}$ (`rademacherTerm_eq_bessel`, proved),
$p(n) = \dfrac{2\pi}{(24n-1)^{3/4}} \sum_{k \ge 1} \dfrac{A_k(n)}{k}
  I_{3/2}\Bigl(\dfrac{\pi\sqrt{24n-1}}{6k}\Bigr)$.

### Proof strategy

1. *Farey dissection.* Hardy and Ramanujan dissect their circle by Farey arcs whose order is
   tied to $n$ (about $\sqrt n$); the result is an asymptotic series, which Lehmer later showed
   to be divergent. Rademacher instead keeps $n$ fixed and lets the path depend on a free
   parameter $N$: the circle $|q| = e^{-2\pi/N^2}$ dissected by the Farey fractions $h/k$ of
   order $N$ or, in the later version, the path in the $\tau$-plane along the Ford circles
   $C(h,k)$ (centre $h/k + i/(2k^2)$, radius $1/(2k^2)$) for all Farey fractions of order $N$.
   Every reduced fraction $h/k$ eventually contributes, and $N \to \infty$ at the end.
2. *Transformation formula for $\eta$.* Near $e^{2\pi i h/k}$ one writes $\tau = (h + iz)/k$ and
   $\tau' = (H + i/z)/k$ with $hH \equiv -1 \pmod k$. The general transformation law
   (`eta_modular_transformation`) gives
   $P(e^{2\pi i \tau}) = \omega_{h,k}\, \sqrt z\,
   \exp\Bigl(\dfrac{\pi}{12 k z} - \dfrac{\pi z}{12 k}\Bigr) P(e^{2\pi i \tau'})$, where
   $P(e^{2\pi i\tau'}) = 1 + O(e^{-2\pi \operatorname{Re}(1/z)/k})$.
3. *Main terms.* Replacing $P(e^{2\pi i\tau'})$ by $1$ and completing each arc to a full circle
   in the $z$-plane produces a Bessel integral, which equals the $k$-th term of the series; the
   sum over $h$ assembles the exponential sum $A_k(n)$.
4. *Error terms and exactness.* The contributions of $P(e^{2\pi i \tau'}) - 1$ and of the
   completed arcs are $O(N^{-1/2})$, and therefore vanish as $N \to \infty$. This is the content
   of `tsum_rademacherTerm`.
5. *Absolute convergence.* The kernel derivative is $O(k^{-3})$ as $k \to \infty$ and
   $|A_k(n)| \le k$ trivially (`abs_rademacherSum_le`, proved), so the $k$-th term is
   $O(k^{-3/2})$ (`abs_rademacherTerm_le`); this already gives `summable_rademacherTerm`.
   Sharper bounds for the Kloosterman-type sums $A_k(n)$, namely Lehmer's
   $|A_k(n)| < 2 k^{5/6}$ [Leh] and bounds of square-root quality,
   $A_k(n) = O(k^{1/2 + \varepsilon})$, which follow from the Selberg–Whiteman evaluation of
   $A_k(n)$, give effective remainder estimates: $O(\sqrt n)$ terms determine $p(n)$ by rounding.
6. *Poincaré series.* Conceptually, $q^{-1/24} P(q) = 1/\eta(\tau)$ is a weakly holomorphic
   modular form of weight $-1/2$ with multiplier system $\bar v_\eta$, and Rademacher's formula
   is its expansion as a Poincaré series: $A_k(n)$ is the Kloosterman sum attached to the
   multiplier system, and $I_{3/2}$ is the Bessel function belonging to weight $-1/2$. In
   negative weight the Poincaré series does not converge absolutely, which is why the circle
   method (or the analytic continuation of Maass–Poincaré series) is needed.

Prerequisites missing from Mathlib: Dedekind sums and the multiplier system of $\eta$, modified
Bessel functions $I_\nu$, Farey dissections and Ford circles, Kloosterman sum bounds.
-/

section Rademacher

/-- The sawtooth function $((x))$: $x - \lfloor x \rfloor - \tfrac12$ for $x \notin \mathbb{Z}$,
and $0$ for $x \in \mathbb{Z}$. -/
def sawtooth (x : ℝ) : ℝ := if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

/-- The **Dedekind sum** $s(h, k) = \sum_{r \bmod k} ((r/k))\,((hr/k))$. -/
def dedekindSum (h : ℤ) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range k, sawtooth ((r : ℝ) / k) * sawtooth ((h : ℝ) * r / k)

theorem sawtooth_neg (x : ℝ) : sawtooth (-x) = -sawtooth x := by
  unfold sawtooth
  by_cases hx : Int.fract x = 0
  · simp [hx, Int.fract_neg_eq_zero.mpr hx]
  · have hx' : Int.fract (-x) ≠ 0 := fun h => hx (Int.fract_neg_eq_zero.mp h)
    simp only [hx, hx', ↓reduceIte]
    rw [Int.fract_neg hx]
    ring

theorem sawtooth_add_intCast (x : ℝ) (m : ℤ) : sawtooth (x + m) = sawtooth x := by
  unfold sawtooth
  rw [Int.fract_add_intCast]

/-- The Dedekind sum is odd in its first argument: $s(-h, k) = -s(h, k)$. -/
theorem dedekindSum_neg (h : ℤ) (k : ℕ) : dedekindSum (-h) k = -dedekindSum h k := by
  unfold dedekindSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [show ((-h : ℤ) : ℝ) * r / k = -((h : ℝ) * r / k) by push_cast; ring, sawtooth_neg]
  ring

/-- The Dedekind sum is $k$-periodic in its first argument: $s(h + k, k) = s(h, k)$. -/
theorem dedekindSum_add_self (h : ℤ) (k : ℕ) : dedekindSum (h + k) k = dedekindSum h k := by
  unfold dedekindSum
  refine Finset.sum_congr rfl fun r hr => ?_
  have hk : (k : ℝ) ≠ 0 := by
    have := Finset.mem_range.mp hr
    exact_mod_cast (Nat.zero_lt_of_lt this).ne'
  rw [show ((h + k : ℤ) : ℝ) * r / k = (h : ℝ) * r / k + ((r : ℤ) : ℝ) by
    push_cast; field_simp, sawtooth_add_intCast]

theorem dedekindSum_self_sub (h : ℤ) (k : ℕ) : dedekindSum (k - h) k = -dedekindSum h k := by
  rw [show (k : ℤ) - h = -h + k by ring, dedekindSum_add_self, dedekindSum_neg]

/-- The root of unity $\omega_{h,k} = e^{\pi i s(h,k)}$ from the multiplier system of $\eta$. -/
def rademacherOmega (h : ℤ) (k : ℕ) : ℂ :=
  Complex.exp (((π * dedekindSum h k : ℝ) : ℂ) * Complex.I)

/-- The exponential sum
$A_k(n) = \sum_{0 \le h < k,\ \gcd(h,k) = 1} \omega_{h,k}\, e^{-2\pi i n h / k}$ as a complex
number. For $k = 1$ the sum consists of the single term $h = 0$, so $A_1(n) = 1$. -/
def rademacherSumComplex (k n : ℕ) : ℂ :=
  ∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k),
    rademacherOmega (h : ℤ) k * Complex.exp (((-(2 * π * n * h / k) : ℝ) : ℂ) * Complex.I)

/-- The Kloosterman-type sum $A_k(n)$ of Rademacher's formula, as a real number.

$A_k(n)$ is defined by complex exponentials but is real: $h \mapsto k - h$ permutes the reduced
residues and conjugates the summand, because $s(k - h, k) = -s(h, k)$
(`rademacherSumComplex_im`, proved below). The real value is defined as the real part of
`rademacherSumComplex`, so that `rademacherSumComplex k n = (rademacherSum k n : ℂ)`
(`rademacherSumComplex_eq_ofReal`); explicitly
$A_k(n) = \sum_h \cos\bigl(\pi s(h,k) - 2\pi n h / k\bigr)$ (`rademacherSum_eq_sum_cos`). -/
def rademacherSum (k : ℕ) (n : ℕ) : ℝ := (rademacherSumComplex k n).re

/-- $A_k(n) = \sum_{0 \le h < k,\ \gcd(h,k)=1} \cos\bigl(\pi s(h,k) - 2\pi n h/k\bigr)$. -/
theorem rademacherSum_eq_sum_cos (k n : ℕ) :
    rademacherSum k n = ∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k),
      Real.cos (π * dedekindSum (h : ℤ) k - 2 * π * n * h / k) := by
  unfold rademacherSum rademacherSumComplex rademacherOmega
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, Complex.exp_ofReal_mul_I_re,
    ← sub_eq_add_neg]

theorem rademacherSumComplex_im_eq_sum_sin (k n : ℕ) :
    (rademacherSumComplex k n).im = ∑ h ∈ (Finset.range k).filter (fun h => Nat.Coprime h k),
      Real.sin (π * dedekindSum (h : ℤ) k - 2 * π * n * h / k) := by
  unfold rademacherSumComplex rademacherOmega
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, Complex.exp_ofReal_mul_I_im,
    ← sub_eq_add_neg]

/-- **$A_k(n)$ is real.** The involution $h \mapsto k - h$ of the reduced residues modulo $k$
replaces each summand by its complex conjugate, because $s(k - h, k) = -s(h, k)$
(`dedekindSum_self_sub`). -/
theorem rademacherSumComplex_im (k n : ℕ) : (rademacherSumComplex k n).im = 0 := by
  rw [rademacherSumComplex_im_eq_sum_sin]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · -- `k = 0` (empty sum) and `k = 1` (the single term `h = 0`)
    interval_cases k
    · simp
    · simp [dedekindSum, sawtooth]
  · -- `k ≥ 2`: pair `h` with `k - h`
    set S := (Finset.range k).filter (fun h => Nat.Coprime h k) with hS
    set f : ℕ → ℝ := fun h => Real.sin (π * dedekindSum (h : ℤ) k - 2 * π * n * h / k) with hf
    have hmem : ∀ h ∈ S, 1 ≤ h ∧ h < k := by
      intro h hh
      rw [hS, Finset.mem_filter, Finset.mem_range] at hh
      refine ⟨?_, hh.1⟩
      rcases Nat.eq_zero_or_pos h with rfl | hpos
      · have := hh.2
        rw [Nat.coprime_zero_left] at this
        omega
      · exact hpos
    have hmap : ∀ h ∈ S, k - h ∈ S := by
      intro h hh
      obtain ⟨h1, h2⟩ := hmem h hh
      rw [hS, Finset.mem_filter, Finset.mem_range] at hh ⊢
      exact ⟨by omega, (Nat.coprime_self_sub_left h2.le).mpr hh.2⟩
    have hinv : ∀ h ∈ S, k - (k - h) = h := fun h hh => Nat.sub_sub_self (hmem h hh).2.le
    have hneg : ∀ h ∈ S, f (k - h) = -f h := by
      intro h hh
      obtain ⟨h1, h2⟩ := hmem h hh
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      simp only [hf]
      rw [Nat.cast_sub h2.le, Nat.cast_sub h2.le, dedekindSum_self_sub,
        show π * -dedekindSum (h : ℤ) k - 2 * π * n * ((k : ℝ) - h) / k =
          -(π * dedekindSum (h : ℤ) k - 2 * π * n * h / k) - n * (2 * π) by field_simp; ring,
        Real.sin_sub_nat_mul_two_pi, Real.sin_neg]
    have hsum : ∑ h ∈ S, f h = ∑ h ∈ S, f (k - h) :=
      Finset.sum_nbij' (fun h => k - h) (fun h => k - h) hmap hmap hinv hinv
        (fun h hh => by rw [hinv h hh])
    have hT : ∑ h ∈ S, f h = -∑ h ∈ S, f h := by
      rw [← Finset.sum_neg_distrib]
      exact hsum.trans (Finset.sum_congr rfl hneg)
    linarith

theorem rademacherSumComplex_eq_ofReal (k n : ℕ) :
    rademacherSumComplex k n = (rademacherSum k n : ℂ) := by
  apply Complex.ext
  · simp [rademacherSum]
  · simp [rademacherSumComplex_im]

/-- The trivial bound $|A_k(n)| \le k$, which suffices for absolute convergence. -/
theorem abs_rademacherSum_le (k n : ℕ) : |rademacherSum k n| ≤ k := by
  rw [rademacherSum_eq_sum_cos]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun h _ => Real.abs_cos_le_one _).trans ?_
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range k).le

/-- $A_1(n) = 1$. -/
theorem rademacherSum_one (n : ℕ) : rademacherSum 1 n = 1 := by
  simp [rademacherSum_eq_sum_cos, dedekindSum, sawtooth]

/-- Rademacher's kernel
$x \mapsto \sinh\bigl(\tfrac{\pi}{k} \sqrt{\tfrac23 (x - \tfrac1{24})}\bigr) \big/
\sqrt{x - \tfrac1{24}}$. -/
def rademacherKernel (k : ℕ) (x : ℝ) : ℝ :=
  Real.sinh (π / k * √(2 / 3 * (x - 1 / 24))) / √(x - 1 / 24)

/-- The derivative of `rademacherKernel k` in closed form: with $u = x - \tfrac1{24}$ and
$y = \tfrac{\pi}{k}\sqrt{\tfrac23 u}$, it is
$\dfrac{\pi\sqrt{2/3}}{k} \cdot \dfrac{\cosh y}{2u} - \dfrac{\sinh y}{2 u \sqrt u}$
(see `hasDerivAt_rademacherKernel`). -/
def rademacherKernelDeriv (k : ℕ) (x : ℝ) : ℝ :=
  π * √(2 / 3) / k * Real.cosh (π / k * √(2 / 3 * (x - 1 / 24))) / (2 * (x - 1 / 24)) -
    Real.sinh (π / k * √(2 / 3 * (x - 1 / 24))) / (2 * (x - 1 / 24) * √(x - 1 / 24))

/-- `rademacherKernelDeriv k` is the derivative of `rademacherKernel k` on $(1/24, \infty)$. -/
theorem hasDerivAt_rademacherKernel (k : ℕ) {x : ℝ} (hx : 1 / 24 < x) :
    HasDerivAt (rademacherKernel k) (rademacherKernelDeriv k x) x := by
  have hu : 0 < x - 1 / 24 := sub_pos.mpr hx
  have hs : 0 < √(x - 1 / 24) := Real.sqrt_pos.mpr hu
  have h1 : HasDerivAt (fun y : ℝ => y - 1 / 24) 1 x := (hasDerivAt_id x).sub_const _
  have h2 : HasDerivAt (fun y : ℝ => √(y - 1 / 24)) (1 / (2 * √(x - 1 / 24))) x :=
    h1.sqrt hu.ne'
  have h3 : HasDerivAt (fun y : ℝ => π / k * √(2 / 3 * (y - 1 / 24)))
      (π / k * (√(2 / 3) * (1 / (2 * √(x - 1 / 24))))) x := by
    have hfun : (fun y : ℝ => π / k * √(2 / 3 * (y - 1 / 24))) =
        fun y : ℝ => π / k * (√(2 / 3) * √(y - 1 / 24)) := by
      funext y
      rw [Real.sqrt_mul (by norm_num)]
    rw [hfun]
    exact (h2.const_mul _).const_mul _
  have h4 := h3.sinh.div h2 hs.ne'
  have hsq : x - 1 / 24 = √(x - 1 / 24) ^ 2 := (Real.sq_sqrt hu.le).symm
  have hs' : √(x - 1 / 24) ≠ 0 := hs.ne'
  refine h4.congr_deriv ?_
  unfold rademacherKernelDeriv
  generalize Real.cosh (π / k * √(2 / 3 * (x - 1 / 24))) = c
  generalize Real.sinh (π / k * √(2 / 3 * (x - 1 / 24))) = sh
  generalize √(x - 1 / 24) = s at hsq hs' ⊢
  rw [hsq]
  field_simp

/-- The $k$-th term of Rademacher's series:
$\dfrac{1}{\pi\sqrt 2}\, A_k(n)\, \sqrt k\, \dfrac{d}{dx}\Big|_{x = n}
\dfrac{\sinh\bigl(\frac{\pi}{k}\sqrt{\frac23 (x - \frac1{24})}\bigr)}{\sqrt{x - \frac1{24}}}$.

The derivative is inserted in closed form (`rademacherKernelDeriv`), so that the definition
does not depend on `deriv`. It is meaningful for $n \ge 1$, where $n - \tfrac1{24} > 0$; for
$n = 0$ the real square roots are clamped to $0$ and the value is not meaningful. -/
def rademacherTerm (k : ℕ) (n : ℕ) : ℝ :=
  1 / (π * √2) * rademacherSum k n * √(k : ℝ) * rademacherKernelDeriv k n

/-- The modified Bessel function of the first kind of order $3/2$ in closed form,
$I_{3/2}(z) = \sqrt{\dfrac{2}{\pi z}} \Bigl(\cosh z - \dfrac{\sinh z}{z}\Bigr)$ for $z > 0$.
(Mathlib has no modified Bessel functions $I_\nu$ yet.) -/
def besselIThreeHalves (z : ℝ) : ℝ :=
  √(2 / (π * z)) * (Real.cosh z - Real.sinh z / z)

/-- Bessel form of the terms of Rademacher's series:
$\dfrac{2\pi}{(24n-1)^{3/4}} \cdot \dfrac{A_k(n)}{k} \cdot
I_{3/2}\Bigl(\dfrac{\pi\sqrt{24n-1}}{6k}\Bigr)$. This is an algebraic identity between
radicals; it is proved by expressing every radical through $\sqrt 2$, $\sqrt 3$, $\sqrt k$,
$w = \sqrt{24n-1}$ and $\sqrt w$. -/
theorem rademacherTerm_eq_bessel (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    rademacherTerm k n =
      2 * π / (24 * (n : ℝ) - 1) ^ (3 / 4 : ℝ) * (rademacherSum k n / k) *
        besselIThreeHalves (π * √(24 * (n : ℝ) - 1) / (6 * k)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX : (0 : ℝ) < 24 * n - 1 := by linarith
  have hw : 0 < √(24 * (n : ℝ) - 1) := Real.sqrt_pos.mpr hX
  have hwsq : √(24 * (n : ℝ) - 1) ^ 2 = 24 * n - 1 := Real.sq_sqrt hX.le
  have hsw : 0 < √√(24 * (n : ℝ) - 1) := Real.sqrt_pos.mpr hw
  have hswsq : √√(24 * (n : ℝ) - 1) ^ 2 = √(24 * (n : ℝ) - 1) := Real.sq_sqrt hw.le
  have hsk : 0 < √(k : ℝ) := Real.sqrt_pos.mpr hk'
  have hsksq : √(k : ℝ) ^ 2 = k := Real.sq_sqrt hk'.le
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr two_pos
  have h2sq : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt two_pos.le
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr three_pos
  have h3sq : √(3 : ℝ) ^ 2 = 3 := Real.sq_sqrt three_pos.le
  have hπ : π ≠ 0 := Real.pi_ne_zero
  -- all radicals in terms of `√2`, `√3`, `√k`, `w = √(24 n - 1)` and `√w`
  have e1 : √(2 / 3 : ℝ) = √2 * √3 / 3 := by
    rw [show (2 / 3 : ℝ) = (√2 * √3 / 3) ^ 2 by rw [div_pow, mul_pow, h2sq, h3sq]; norm_num]
    exact Real.sqrt_sq (by positivity)
  have e2 : √((n : ℝ) - 1 / 24) = √(24 * (n : ℝ) - 1) / (2 * √2 * √3) := by
    rw [show (n : ℝ) - 1 / 24 = (√(24 * (n : ℝ) - 1) / (2 * √2 * √3)) ^ 2 by
      rw [div_pow, mul_pow, mul_pow, hwsq, h2sq, h3sq]; ring]
    exact Real.sqrt_sq (by positivity)
  have e3 : π / k * √(2 / 3 * ((n : ℝ) - 1 / 24)) = π * √(24 * (n : ℝ) - 1) / (6 * k) := by
    rw [show 2 / 3 * ((n : ℝ) - 1 / 24) = (√(24 * (n : ℝ) - 1) / 6) ^ 2 by
      rw [div_pow, hwsq]; ring, Real.sqrt_sq (by positivity)]
    ring
  have e4 : (24 * (n : ℝ) - 1) ^ (3 / 4 : ℝ) = √(24 * (n : ℝ) - 1) * √√(24 * (n : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hX.le, ← Real.rpow_add hX]
    norm_num
  have e5 : √(2 / (π * (π * √(24 * (n : ℝ) - 1) / (6 * k)))) =
      2 * √3 * √(k : ℝ) / (π * √√(24 * (n : ℝ) - 1)) := by
    rw [show 2 / (π * (π * √(24 * (n : ℝ) - 1) / (6 * k))) =
        (2 * √3 * √(k : ℝ) / (π * √√(24 * (n : ℝ) - 1))) ^ 2 by
      rw [div_pow, mul_pow, mul_pow, mul_pow, h3sq, hsksq, hswsq]
      field_simp
      ring]
    exact Real.sqrt_sq (by positivity)
  have e6 : (n : ℝ) - 1 / 24 = √(24 * (n : ℝ) - 1) ^ 2 / 24 := by rw [hwsq]; ring
  unfold rademacherTerm rademacherKernelDeriv besselIThreeHalves
  rw [e3, e1, e2, e4, e5, e6]
  have hsk0 : √(k : ℝ) ≠ 0 := hsk.ne'
  have hsw0 : √√(24 * (n : ℝ) - 1) ≠ 0 := hsw.ne'
  have h20 : √(2 : ℝ) ≠ 0 := h2.ne'
  have h30 : √(3 : ℝ) ≠ 0 := h3.ne'
  generalize rademacherSum k n = A
  generalize Real.cosh (π * √(24 * (n : ℝ) - 1) / (6 * k)) = c
  generalize Real.sinh (π * √(24 * (n : ℝ) - 1) / (6 * k)) = sh
  generalize √√(24 * (n : ℝ) - 1) = sw at hswsq hsw0 ⊢
  rw [← hswsq]
  generalize √(k : ℝ) = sk at hsksq hsk0 ⊢
  rw [← hsksq]
  field_simp
  ring

/-- **Dedekind's transformation formula for $\eta$** [Apo, Theorem 3.4]. For
$\begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ with $c > 0$ and
$\operatorname{Im} \tau > 0$,
$$\eta\Bigl(\frac{a\tau + b}{c\tau + d}\Bigr)
= \exp\Bigl(\pi i \Bigl(\frac{a + d}{12 c} + s(-d, c)\Bigr)\Bigr)
\bigl(-i (c\tau + d)\bigr)^{1/2}\, \eta(\tau),$$
with the principal branch of the square root. This is the source of the factors $\omega_{h,k}$
in $A_k(n)$. Terminal obligation; Mathlib currently has the case $\tau \mapsto -1/\tau$ only. -/
theorem eta_modular_transformation (a b d : ℤ) (c : ℕ) (hc : 0 < c)
    (hdet : a * d - b * c = 1) {τ : ℂ} (hτ : 0 < τ.im) :
    ModularForm.eta ((a * τ + b) / (c * τ + d)) =
      Complex.exp (π * Complex.I *
          (((a + d : ℤ) : ℂ) / (12 * c) + ((dedekindSum (-d) c : ℝ) : ℂ))) *
        Complex.sqrt (-Complex.I * (c * τ + d)) * ModularForm.eta τ := by
  sorry

/-- The $k$-th term of Rademacher's series is $O_n(k^{-3/2})$.

Terminal obligation: `abs_rademacherSum_le` together with
$y \cosh y - \sinh y = O(y^3)$ as $y \to 0$, applied to
$y = \tfrac{\pi}{k}\sqrt{\tfrac23 (n - \tfrac1{24})}$. -/
theorem abs_rademacherTerm_le (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, ∀ k : ℕ, 0 < k → |rademacherTerm k n| ≤ C / (k : ℝ) ^ (3 / 2 : ℝ) := by
  sorry

/-- Rademacher's series converges absolutely. -/
theorem summable_rademacherTerm (n : ℕ) (hn : 0 < n) :
    Summable (fun k : ℕ => rademacherTerm (k + 1) n) := by
  obtain ⟨C, hC⟩ := abs_rademacherTerm_le n hn
  have hp : Summable (fun k : ℕ => C * (((k + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    ((summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 3 / 2))).mul_left C
  refine Summable.of_norm_bounded hp fun k => ?_
  rw [Real.norm_eq_abs, ← div_eq_mul_inv]
  exact hC (k + 1) k.succ_pos

/-- The sum of Rademacher's series is $p(n)$.

Terminal obligation: this is the analytic core of [Rad] (steps 1 to 4 of the module docstring). -/
theorem tsum_rademacherTerm (n : ℕ) (hn : 0 < n) :
    ∑' k : ℕ, rademacherTerm (k + 1) n = (partitionFunction n : ℝ) := by
  sorry

/-- **Rademacher's exact formula for the partition function** [Rad]: for $n \ge 1$,
$p(n) = \sum_{k \ge 1}$ `rademacherTerm k n`, the series being absolutely convergent.

The hypothesis `hn : n > 0` is needed because the terms involve $\sqrt{n - 1/24}$ as a real
square root. The summation index is shifted so that `k : ℕ` corresponds to the term $k + 1$. -/
theorem rademacher_exact_series (n : ℕ) (hn : n > 0) :
    HasSum (fun k : ℕ => rademacherTerm (k + 1) n) (partitionFunction n : ℝ) :=
  (summable_rademacherTerm n hn).hasSum_iff.mpr (tsum_rademacherTerm n hn)

/-- The first term of Rademacher's series is asymptotic to the Hardy–Ramanujan main term.
Combined with a bound for the terms $k \ge 2$, this is how Module 4 implies Module 3. Terminal
obligation (elementary real analysis). -/
theorem rademacherTerm_one_isEquivalent :
    (fun n : ℕ => rademacherTerm 1 n) ~[atTop] hardyRamanujanMainTerm := by
  sorry

end Rademacher

end PartitionTheory
