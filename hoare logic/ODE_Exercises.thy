
theory ODEs_Exercises
  imports "Hybrid-Verification.Hybrid_Verification"
begin

dataspace basic_odes = 
  constants 
    N :: int
  assumes 
    Nge0: "0 < N" 
  variables
    x :: real
    y :: real
    z :: real
    v :: real
    t :: real

context basic_odes
begin


subsection ‹ Local flows ›

text ‹ Prove the following lemmas automatically ›

lemma "a ≠ 0 ⟹ vwb_lens x 
  ⟹ local_flow_on [x ↝ a * x + b] x UNIV UNIV (λτ. [x ↝ (x + b/a) * exp (a * τ) - b/a])"
  by local_flow_on_auto 

lemma "local_flow_on [x ↝ v, v ↝ a, t ↝ 1] (x +⇩L v) UNIV UNIV 
  (λτ. [x ↝ a * τ⇧2 / 2 + v * τ + x, v ↝ a * τ + v, t ↝ τ + t])"
  by local_flow_on_auto 

lemma "local_flow_on [x ↝ - y, y ↝ x] (x +⇩L y) UNIV UNIV 
  (λτ. [x ↝ x * cos τ + - 1 * y * sin τ, y ↝ y * cos τ + x * sin τ])"
  by local_flow_on_auto 


text ‹ Suggest a solution for the following ODEs and check that they are correct. ›

(*
left hand-side = differential equation
right hand-side = local flow or solution
*)

lemma "local_flow_on [x ↝ - x] x UNIV UNIV 
  (λτ. [x ↝ x * exp(-τ)])"
  by local_flow_on_auto 

lemma "local_flow_on [x ↝ y] x UNIV UNIV 
  (λτ. [x ↝ x + τ * y])"
  by local_flow_on_auto 

lemma "local_flow_on [x ↝ - x + 1] x UNIV UNIV 
  (λτ. [x ↝ 1 + (x - 1) * exp(-τ)])"
  by local_flow_on_auto 

lemma "local_flow_on [y ↝ - 2] y UNIV UNIV 
  (λτ. [y ↝ y - 2 * τ])"
  by local_flow_on_auto 

lemma "local_flow_on [x ↝ x] x UNIV UNIV 
  (λτ. [x ↝ x * exp(τ)])"
  by local_flow_on_auto 

lemma "local_flow_on [x ↝ a * x] x UNIV UNIV 
  (λτ. [x ↝ x * exp(a * τ)])"
  by local_flow_on_auto 

lemma "local_flow_on [x ↝ - y * x] x UNIV UNIV 
  (λτ. [x ↝ x * exp(-y * τ)])"
  by local_flow_on_auto 


subsection ‹ ODEs ›

text ‹ Decide whether to solve the following problems with invariant or flow reasoning ›

lemma "H{N ≤ x} {x` = 2} {N ≤ x}"
  by dInduct_auto

lemma "H{0 < x} {x` = - x + 1} {0 < x}"
  apply (dGhost z "x*z⇧2 = 1" "-1/2")
    apply dInduct_auto 
  oops

lemma "H{x ≤ 0} {x` = - 2 * x⇧2} {x ≤ 0}"
  by dInduct_auto

lemma "H{0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z} {x` = y, y` = z} {0 ≤ x}"
  apply auto
  oops

lemma "H{N ≤ x} {x` = x^16} {N ≤ x}"
  by dInduct_auto

lemma "a > 0 ⟹ H{x ≥ 0} {x` = v, v` = a | (v ≥ 0)} {x ≥ 0}"
  by dInduct_auto

lemma "(x > 0)⇩e ≤ |{x` = x powr x}] (x > 0)"
  by dInduct_auto

text ‹ Give two proofs of the following statements, one with invariants and one with solutions. ›

lemma "H{x ≤ 0} {x` = - 2} {x ≤ 0}"
  by dInduct

lemma "H{x ≤ 0} {x` = - 2} {x ≤ 0}"
  apply (ode_solve_with "λτ. [x ↝ x - 2 * τ]")

lemma "H{x⇧2 + y⇧2 = 1} {x` = - y, y` = x} {x⇧2 + y⇧2 = 1}"
  by dInduct

lemma "H{x⇧2 + y⇧2 = 1} {x` = - y, y` = x} {x⇧2 + y⇧2 = 1}"
  apply (ode_solve_with "λτ. [x ↝ x * cos τ - y * sin τ, y ↝ y * cos τ + x * sin τ]")
  by (simp add: Groups.add_ac(2))

lemma exp_ghost_arith: "0 < (a::real) ⟷ (∃b. a * b⇧2 = 1)" ― ‹ this is a hint ›
  by (intro iffI exI[where x="1/(sqrt a)"]; clarsimp simp: field_simps)
    (metis less_numeral_extra(1) mult_less_0_iff not_one_less_zero zero_less_mult_iff)

lemma "k > 0 ⟹ H{0 ≤ x} {x` = - k * x} {0 ≤ x}" ― ‹ challenging ›
  apply (ode_solve_with "λτ. [x ↝ x * exp (-k * τ)]")
  by auto

lemma "k > 0 ⟹ H{0 ≤ x} {x` = - k * x} {0 ≤ x}"
  apply (dGhost z "x * z⇧2 = 1" "k / 2")
   apply dInduct_auto
   apply (expr_simp add: exp_ghost_arith)
  oops
  

end


text ‹ Can you prove the following statement automatically? ›

dataspace rotational_dynamics3 =
  constants
    w :: real
    p :: real
  variables 
    x1 :: real 
    x2 :: real 
    d1 :: real
    d2 :: real

context rotational_dynamics3
begin

lemma "H{d1⇧2 + d2⇧2 = w⇧2 * p⇧2 ∧ d1 = - w * x2 ∧ d2 = w * x1} 
  {x1` = d1, x2` = d2, d1` = - w * d2, d2` = w * d1} 
  {d1⇧2 + d2⇧2 = w⇧2 * p⇧2 ∧ d1 = - w * x2 ∧ d2 = w * x1}"
    by dInduct_auto

end


text ‹ Is the following statement true? If it is, provide a proof. ›

context basic_odes
begin

lemma "H{0.5 ≤ x ∧ x ≤ 0.7 ∧ 0 ≤ y ∧ y ≤ 0.3}
    {x` = -x + x * y , y` = - y}
  { ¬ (-0.8 ≥ x ∧ x ≥ -1 ∧ -0.7 ≥ y ∧ y ≥ -1)}"
  oops

end

text ‹ If you have time to spare, give a step-by-step pen-and-paper reasoning of the 
rotational dynamics exercise or, try updating any of the proofs at
@{url "https://github.com/isabelle-utp/Hybrid-Verification/blob/main/Hybrid_Programs/Verification_Examples/ARCH2022_Examples.thy"} ›

end