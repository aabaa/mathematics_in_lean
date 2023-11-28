import Mathlib.Data.Set.Finite
import Mathlib.Logic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
open Classical Finset Nat BigOperators

theorem p_and_q_implies_q_or_p (p q : Prop)(h : p ∧ q) :
  p ∧ q → q ∨ p := by
  simp [h]

theorem example1 (p q r : Prop):
  (p → q → r) → (p → q) → p → r := by
  intros h1 h2 h3; exact h1 h3 (h2 h3)

/--
  期待値の定義
  Ω : ℕ上の有限集合
  P : Ω → ℝ -- 確率関数
  X : Ω → ℝ -- 確率変数
  ∑の都合上，P, X の型は ℕ → ℝ として定義
  E(x) = ∑ x * P(x)
-/
def Ex (Ω : Finset ℕ)(P X : ℕ → ℝ) : ℝ :=
  ∑ x in Ω, (P x) * (X x)

/--
  ite は if-then-else の略
  ite p x y は p が真なら x で，偽なら y を返す
  以下の補題は，p と q が同値なら ite p x y = ite q x y となることを示している
  ※ Leanでは p ↔ q ならば p = q ではないため，証明が必要になる
-/
lemma ite_equiv_iff (p q : Prop)(a b : ℝ) [Decidable p] [Decidable q] :
(p ↔ q) → ite p a b = ite q a b := by
  intro hpq
  by_cases hp: p
  rw [if_pos hp]
  rw [if_pos (hpq.mp ‹p›)]
  rw [if_neg hp]
  have hnq : ¬q := λ hq : q ↦ hp (Iff.mpr hpq hq)
  rw [if_neg hnq]

/--
  Xor' p q は p と q の排他的論理和
  p と q が排他的であれば ite p a b = ite q b a となることを示している
-/
lemma ite_xor (p q : Prop)(a b : ℝ) [Decidable p][Decidable q]:
  (Xor' p q) -> (ite p a b) = (ite q b a) := by
  intro h
  cases' h with h1 h2
  rw [if_pos,if_neg]
  apply h1.right
  apply h1.left
  rw [if_neg,if_pos]
  apply h2.left
  apply h2.right

/--
  a ≥ b と a < b が排他的であることを示す．
-/
lemma xor_ge_lt (a b : ℝ) :
  Xor' (a ≥ b) (a < b) := by
  by_cases h : a ≥ b
  left
  simp [h]
  right
  simp [h]
  exact lt_of_not_ge h


/--
  ite p a 0 + ite p 0 a = a となることを示す．
-/
lemma ite_exchange_zero (p : Prop) (a : ℝ) [Decidable p] :
  (ite p a 0) + (ite p 0 a) = a := by
  by_cases h : p
  rw [if_pos h, if_pos h]
  simp [h]
  rw [if_neg h, if_neg h]
  simp [h]

/--
-/
lemma ite_mul_inequality (a x y : ℝ)(hx: x ≥ 0) :
  ite (y ≥ a) (x * y) 0 >= a * ite (y ≥ a) x 0 := by
  by_cases h : y ≥ a
  rw [if_pos,if_pos]
  simp
  rw [mul_comm]
  have h' : a ≤ y := by exact h
  have hx' : 0 ≤ x := by exact hx
  simp [mul_le_mul_of_nonneg_left,h',hx']
  exact h
  simp [h]
  simp [if_neg h]

/--
  a ≥ 0 ならば ite p a 0 ≥ 0 となることを示す．
-/
lemma ite_ge_zero {p : Prop}{a : ℝ}(ha : a ≥ 0)[Decidable p] :
  ite p a 0 >= 0 := by
  by_cases hp : p
  have h1: ite p a 0 = a := if_pos hp
  simp [h1,ha]
  have h2 : ite p a 0 = 0 := if_neg hp
  simp [h2]

/--
  非負関数の積は非負であることを示す．
-/
lemma nonnegative_functions_multi_ge_0 (f g : ℕ → ℝ)
  (hf: ∀x, f x ≥ 0)(hg: ∀x, g x ≥ 0): (∀x, f x * g x ≥ 0) := by
  intros x
  exact mul_nonneg (hf x) (hg x)

/--
  非負関数の各点の総和は非負であることを示す．
-/
lemma nonnegative_function_sum_ge_0 (Ω : Finset ℕ)(f : ℕ → ℝ)(hf: ∀x, f x ≥ 0):
  (∑ ω in Ω, f ω) ≥ 0 := by
  induction Ω using Finset.induction_on with
  | empty => simp
  | @insert a Ω ha ih =>
  simp [ha]
  have h1 : 0 ≤ f a := by exact hf a
  have h2 : 0 ≤ (∑ ω in Ω, f ω) := by exact ih
  linarith [h1,h2]

/--
  各点での確率の和が 非負であることを示す．
-/
lemma pa_sum_ge_zero {Ω : Finset ℕ}{P X : ℕ → ℝ}{a : ℝ}
  (hP: ∀ ω, P ω ≥ 0)(hX: ∀ ω, X ω ≥ 0):
  (∑ ω in Ω, ite (X ω < a) (P ω * X ω) 0) ≥ 0 := by
  let f := λ ω => ite (X ω < a) (P ω * X ω) 0
  have hm: ∀ x, P x * X x ≥ 0 := nonnegative_functions_multi_ge_0 P X hP hX
  have hf: ∀ω , ite (X ω < a) (P ω * X ω) 0 ≥ 0 := by
    intros ω
    have h1: P ω * X ω ≥ 0 := hm ω
    have h2: ite (X ω < a) (P ω * X ω) 0 ≥ 0 := ite_ge_zero h1
    exact h2
  apply nonnegative_function_sum_ge_0 Ω f hf

/--
  期待値の分割
  E(X) =  Σ ω P(X = ω)
       =  Σ_{ω ≧ a} ω * P(X = ω) + Σ_{ω < a} ω * P(X = ω)
-/
lemma expectation_split_equality {Ω : Finset ℕ}{P X : ℕ → ℝ}{a : ℝ} :
  (∑ ω in Ω, ite (X ω < a) (P ω * X ω) 0) +
  (∑ ω in Ω, ite (X ω ≥ a) (P ω * X ω) 0)
  = Ex Ω P X := by
  rw [<-Finset.sum_add_distrib]
  congr 1
  ext ω
  let h1 := X ω < a
  let h2 := X ω ≥ a
  have h3: Xor' h2 h1 := xor_ge_lt (X ω) a
  have h4: ite h2 (P ω * X ω) 0 = ite h1 0 (P ω * X ω) := by
    rw [ite_xor h2 h1 (P ω * X ω)]
    simp [h3]
  simp [ite_exchange_zero,h3,h4]

/--
  Σ_{ω ≧ a} ω * P(X = ω) + Σ_{ω < a} ω * P(X = ω) ≥ Σ_{ω ≧ a} ω * P(X = ω)
-/
lemma prob_inquality_0 {Ω : Finset ℕ}{P X : ℕ → ℝ}{a : ℝ}
  (hP : ∀ ω, P ω ≥ 0)(hX : ∀ ω, X ω ≥ 0) :
   (∑ ω in Ω, ite (X ω < a) (P ω * X ω) 0)
 + (∑ ω in Ω, ite (X ω ≥ a) (P ω * X ω) 0)
 ≥ (∑ ω in Ω, ite (X ω ≥ a) (P ω * X ω) 0) := by
  simp
  have h1: (∑ ω in Ω, ite (X ω < a) (P ω * X ω) 0) ≥ 0 := pa_sum_ge_zero hP hX
  exact h1

/--
  任意の非負関数 f, g に対して，f(x) ≥ g(x) ならば Σ f(x) ≥ Σ g(x) となることを示す．
-/
lemma sum_fun_inequality {Ω : Finset ℕ}{f g : ℕ → ℝ}{a : ℝ}
  (hfg: ∀ x, f x ≥ g x) :
  (∑ ω in Ω, f ω) ≥ (∑ ω in Ω, g ω) := by
  induction Ω using Finset.induction_on with
  | empty => simp
  | @insert a Ω ha ih =>
    simp [ha]
    have ih' : (∑ ω in Ω, g ω) ≤ (∑ ω in Ω, f ω) := by exact ih
    have h1 : g a ≤ f a := by exact hfg a
    linarith

/--
  ∑ E(X ≥ a) ≥ a * ∑ P(X ≥ a) となることを示す．
-/
lemma prob_inquality_1 {Ω : Finset ℕ}{P X : ℕ → ℝ}{a : ℝ}
    (hP : ∀ ω, P ω ≥ 0) :
    (∑ ω in Ω, ite (X ω ≥ a) (P ω * X ω) 0)
  ≥ (∑ ω in Ω, a * ite (X ω ≥ a) (P ω) 0) := by
  let f := λ ω => ite (X ω ≥ a) (P ω * X ω) 0
  let g := λ ω => a * ite (X ω ≥ a) (P ω) 0
  have h1: ∀ ω : ℕ , f ω ≥ g ω := by
    intros ω
    have hP' : P ω ≥ 0 := hP ω
    let x := P ω
    let y := X ω
    apply ite_mul_inequality a x y hP'
  apply @sum_fun_inequality Ω f g a h1

/--
  Σ a * f(ω) = a * Σ f(ω) となることを示す．
-/
lemma mul_sum_func {Ω : Finset ℕ}{f : ℕ → ℝ}{a : ℝ} :
   (∑ ω in Ω, a * f ω) = a * (∑ ω in Ω, f ω) := by
  induction Ω using Finset.induction_on with
  | empty => simp
  | @insert a Ω ha ih =>
    simp [ha]
    rw [left_distrib,ih]

/--
  a * Σ P(X ≥ a) = Σ a * P(X ≥ a) となることを示す．
-/
lemma prob_inquality_2 {Ω : Finset ℕ}{P X : ℕ → ℝ}{a : ℝ} :
    (∑ ω in Ω, a * ite (X ω ≥ a) (P ω) 0)
  = a * (∑ ω in Ω, ite (X ω ≥ a) (P ω) 0) := by
  apply mul_sum_func

/-
  マルコフの不等式
  任意の確率変数 X (> 0) と a > 0 に対して，a * P(X ≧ a) ≦ E(X) が成り立つ

  証明の流れ
  E(X) =  Σ ω P(X = ω)
       =  Σ_{ω ≧ a} ω * P(X = ω) + Σ_{ω < a} ω * P(X = ω)
       ≧ Σ_{ω ≧ a} ω * P(X = ω)
       ≧ Σ_{ω ≧ a} a * P(X = ω)
       = a * P(|X| ≧ a)
-/
theorem markov_inequality {Ω : Finset ℕ} (P X : ℕ → ℝ)(a : ℝ)
  (hP : ∀ ω, P ω ≥ 0)(hX : ∀ ω, X ω ≥ 0)(ha : a > 0) :
  a * (∑ ω in Ω, ite (X ω ≥ a) (P ω) 0) ≤ (Ex Ω P X) := by
  calc
  (Ex Ω P X) = (∑ ω in Ω, ite (X ω < a) (P ω * X ω) 0)
             + (∑ ω in Ω, ite (X ω ≥ a) (P ω * X ω) 0) := by rw [<- expectation_split_equality]
           _ ≥ (∑ ω in Ω, ite (X ω ≥ a) (P ω * X ω) 0) := prob_inquality_0 hP hX
           _ ≥ (∑ ω in Ω, a * ite (X ω ≥ a) (P ω) 0) := prob_inquality_1 hP
           _ = a * (∑ ω in Ω, ite (X ω ≥ a) (P ω) 0) := prob_inquality_2
