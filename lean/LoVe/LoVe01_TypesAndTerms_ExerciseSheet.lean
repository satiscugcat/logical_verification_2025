/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
  fun a => a

def K : α → β → α :=
  fun a b => a

def C : (α → β → γ) → β → α → γ :=
  fun abg b a => abg a b 

def projFst : α → α → α :=
  fun a₁ a₂ => a₁

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  fun a₁ a₂ => a₂

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  fun abg a ag b => ag a 


/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. Start with an empty context. You might find the
characters `–` (to draw horizontal bars) and `⊢` useful. -/

/-

  ————————————————————————————————————————————— Var  —————————————————————————————————————— Var 
  abg : (α → β → γ), b: β, a: α  ⊢ abg : α → β → γ   abg : (α → β → γ), b: β, a: α  ⊢ a : α
  ——————————————————————————————————————————————————————————————————————————————————————— App
  abg : (α → β → γ), b: β, a: α  ⊢ abg a : β → γ   —————————————————————————————————————— Var
                                                   abg : (α → β → γ), b: β, a: α  ⊢ b : β 
  ——————————————————————————————————————————————————————————————————————————————————————— App
  abg : (α → β → γ), b: β, a: α  ⊢ abg a b : γ
  ——————————————————————————————————————————————————————— Fun
  abg : (α → β → γ), b: β  ⊢  fun a : α ↦ abg a b : α → γ
  ——————————————————————————————————————————————————————————————————— Fun
  abg : (α → β → γ) ⊢ (fun b : β ↦ (fun a : α ↦ abg a b)) : β → α → γ
  ———————————————————————————————————————————————————————————————————————————————————————————— Fun
  ∅ ⊢ (fun abg : (α → β → γ) ↦ (fun b : β ↦ (fun a : α ↦ abg a b) )) : (α → β → γ) → β → α → γ

-/
-- write your solution in a comment here or on paper

end LoVe
