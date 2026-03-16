/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Exercise 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Even and Odd

The `Even` predicate is `True` for even numbers and `False` for odd numbers. -/

#check Even

/- We define `Odd` as the negation of `Even`: -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` or `induction` is useful to reason about hypotheses of the form
`Even …`. -/

@[simp] theorem Odd_1 :
    Odd 1 :=
  by
    intro h
    cases h
 
/- 1.2. Prove that 3 and 5 are odd. -/
@[simp] theorem Odd_3 :
    Odd 1 :=
  by
    intro h
    cases h
@[simp] theorem Odd_5 :
    Odd 1 :=
  by
    intro h
    cases h

-- enter your answer here

/- 1.3. Complete the following proof by structural induction. -/

theorem Even_two_times :
    ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 => Even.add_two _ (Even_two_times m)


/- ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check Score

/- 2.1. Define an inductive predicate that returns `True` if the server is
ahead of the receiver and that returns `False` otherwise. -/


inductive ServAhead : Score → Prop
| vs {m n: ℕ} (hgt: m > n) : ServAhead (Score.vs m n)
| advServ : ServAhead (Score.advServ)
| gameServ : ServAhead (Score.gameServ)

/- 2.2. Validate your predicate definition by proving the following theorems. -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
    ServAhead (Score.vs m n) :=
  ServAhead.vs hgt

theorem ServAhead_advServ :
    ServAhead Score.advServ :=
  ServAhead.advServ

theorem not_ServAhead_advRecv :
    ¬ ServAhead Score.advRecv :=
  by
    intros h
    cases h

theorem ServAhead_gameServ :
    ServAhead Score.gameServ :=
  ServAhead.gameServ

theorem not_ServAhead_gameRecv :
    ¬ ServAhead Score.gameRecv :=
  by
    intros h
    cases h

/- 2.3. Compare the above theorem statements with your definition. What do you
observe? -/
-- They are similar? I do not understand the question.
-- enter your answer here


/- ## Question 3: Binary Trees

3.1. Prove the converse of `IsFull_mirror`. You may exploit already proved
theorems (e.g., `IsFull_mirror`, `mirror_mirror`). -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_IsFull {α : Type} :
    ∀t : Tree α, IsFull (mirror t) → IsFull t :=
  by
    intros t
    rw [<- mirror_mirror t, mirror_mirror  (mirror t)]
    apply IsFull_mirror 

/- 3.2. Define a `map` function on binary trees, similar to `List.map`. -/

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β 
  | Tree.nil => Tree.nil
  | Tree.node v l r => Tree.node (f v) (Tree.map f l) (Tree.map f r)

/- 3.3. Prove the following theorem by case distinction. -/

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
    ∀t : Tree α, Tree.map f t = Tree.nil ↔ t = Tree.nil :=
  by
    intros t
    apply Iff.intro
    {
      induction t with
      | nil => simp [map]
      | node v l r ihl ihr => 
        intro h
        cases h
    }
    {
      intros h   
      rw [h]
      simp [map]
    }
    
    

/- 3.4 (**optional**). Prove the following theorem by rule induction. -/

theorem map_mirror {α β : Type} (f : α → β) :
    ∀t : Tree α, IsFull t → IsFull (Tree.map f t) :=
  by
    intros t h
    induction h with
    | nil => simp [Tree.map]; constructor
    | node v l r hl hr hiff hl_ih hr_ih => 
      constructor
      { assumption }
      { assumption }
      { apply Iff.intro 
        { intros h
          cases hiff
          rw [Tree.map_eq_empty_iff] at h
          rw [Tree.map_eq_empty_iff]
          apply mp; assumption}
        { intros h
          cases hiff
          rw [Tree.map_eq_empty_iff] at h
          rw [Tree.map_eq_empty_iff]
          apply mpr; assumption}}
      
    

end LoVe
