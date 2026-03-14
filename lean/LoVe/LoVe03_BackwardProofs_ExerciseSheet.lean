/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics such as `intro`,
`apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
    a → a :=
  by
    intro ha
    exact ha

theorem K (a b : Prop) :
    a → b → b :=
  by
    intros _ hb
    exact hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  by
    intros habc hb ha
    apply habc
    exact ha
    exact hb

theorem proj_fst (a : Prop) :
    a → a → a :=
  by
    intros ha _
    exact ha

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  by
    intros _ ha
    exact ha

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  by
    intros _ ha hac _
    apply hac
    exact ha

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  by
    intros hab hnb ha
    apply hnb
    apply hab
    exact ha
    

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  by
    apply Iff.intro
    {
      intro h
      apply And.intro
      {
        intro x
        apply And.left
        apply h
      }
      {
        intro x
        apply And.right
        apply h
      }
    }
    {
      intro h
      intro x
      apply And.intro
      apply And.left h
      apply And.right h
    }


/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 :=
  by
    induction n with
    | zero => simp [mul]
    | succ n' ih => 
      simp [mul, add_zero]
      exact ih

#check add_succ
theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n :=
  by
    induction n with
    | zero => simp [mul, add]
    | succ n' ih => 
           simp [mul]
           rw [add_succ, add_comm _ (n' + 1), add_succ, ih]
           rw [<- add_assoc, add_comm n' _]
           

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  by
    induction n with
    | zero => simp [mul, add, mul_zero]
    | succ n' ih =>
      simp [mul_succ, mul, add]
      rw [ih]
      apply add_comm
      

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  by
    induction n with
    | zero => simp [mul, add]
    | succ n' ih => 
      simp [mul, add]
      rw [mul_add, ih]
      
    

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/
 
theorem add_mul (l m n : ℕ) :
    mul (add l m) n = add (mul n l) (mul n m) :=
  by
    induction n with
    | zero => 
      rw [mul_comm 0, mul_comm 0]
      simp [mul, add]
    | succ n' ih =>
      rw [mul_comm (n' + 1), mul_comm (n' + 1)]
      simp [mul, add]
      rw [mul_comm l n', mul_comm m n']
      rw [ih]
      simp [add_assoc, add_comm]
      rw [<- add_assoc m, add_comm m, add_assoc _ m]

/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

theorem Peirce_of_EM :
    ExcludedMiddle → Peirce :=
  by
    rw [ExcludedMiddle, Peirce]
    intros EM a b ab_a
    apply Or.elim (EM a)
    intro ha; exact ha
    intro nha
    apply ab_a
    intro ha
    apply False.elim
    apply nha ha
    
/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
    Peirce → DoubleNegation :=
  by
    rw [Peirce, DoubleNegation]
    intros pierce a hnna
    apply pierce (a) (¬a)
    intro h
    apply False.elim
    apply hnna
    intro ha
    apply hnna
    apply h
    exact ha
    

/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
  by
    rw [DoubleNegation, ExcludedMiddle]
    intros dne a
    apply dne
    intro h
    have : ¬ a ∧ ¬¬a :=
      by
        apply And.intro
        intro ha
        apply h
        apply Or.inl ha

        intro hna
        apply h
        apply Or.inr hna
    apply And.right this
    exact And.left this 
    

end SorryTheorems

end BackwardProofs

end LoVe
