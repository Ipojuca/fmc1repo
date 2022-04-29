
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------
theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hP,
  intro hnnP,
  contradiction, 
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro  hnnP,
  by_cases hP : P,
  exact hP,
  contradiction,
  
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  apply doubleneg_elim,
  apply doubleneg_intro, 
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h,
  cases h with hP hQ,
    right,
    exact hP,
    left,
    exact hQ,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h with hP hQ,
    split,
    exact hQ,
    exact hP,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros h hp,
  cases h with hnP hQ,
    contradiction,
    exact hQ,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros h hnP,
  cases h with hnP hQ,
    contradiction,
    exact hQ,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros h hnQ hP,
  apply hnQ,
  apply h,
  exact hP,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros h hP,
  by_contra hQ,
    apply h,
    exact hQ,
    exact hP, 
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  apply impl_as_contrapositive,
  apply impl_as_contrapositive_converse,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  apply h,
  
  by_cases hP : P,
    left,
    exact hP,
    right,
    exact hP,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro hnP,
  apply hnP,
  apply h,
  intro hp,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro h,
  intro hnPnQ,
  cases h with hP,
    cases hnPnQ with hnP hnQ,
      contradiction,
    cases hnPnQ with hnP hnQ,
      contradiction,

end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro h,
  intro hnPnQ,
  cases hnPnQ with hnP hnQ,
    cases h with hP hQ,
      contradiction,
    cases h with hP hQ,
      contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro hP,
  apply h,
  left,
  exact hP,
  intro hQ,
  apply h,
  right,
  exact hQ,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro h,
  intro hPQ,
  cases h with hnP hnQ,
    cases hPQ with hP hQ,
      contradiction,
      contradiction,
end
-- Prove de Morgan's.

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro hnPQ,
  by_cases hP : P,
    left,
    intro hQ,
    have hPQ : P ∧ Q, from and.intro hP hQ,
      contradiction,
  right,
  exact hP,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros hOr hAnd,
  cases hOr,
  cases hAnd,
  apply hOr,
  exact hAnd_right,
  cases hAnd,
  apply hOr,
  exact hAnd_left,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  apply demorgan_conj,
  apply demorgan_conj_converse,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  apply demorgan_disj,
  apply demorgan_disj_converse,

end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with hP hQR,
    cases hQR with hQ hR,
        left,
        split,
        exact hP,
        exact hQ,
    right,
    split,
    exact hP,
    exact hR,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  cases h with hPQ hPR,
    cases hPQ with hP hQ,
      split,
      exact hP,
      left,
      exact hQ,
    cases hPR with hP hR,
      split,
      exact hP,
      right,
      exact hR,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  split,
  cases h with hP hQR,
    left, 
    exact hP,
    cases hQR with hQ hR,
      right,
      exact hQ,
  cases h with hP hQR,
    left,
    exact hP,
    right,
    cases hQR with hQ hR,
      exact hR,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with hPQ hPR, 
    cases hPR with hP hR,
      left,
      exact hP,
    cases hPQ with hP hQ,
        left,
        exact hP,
    have hQR : Q ∧ R, from and.intro hQ hR,
       right,
       exact hQR,
  
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros h hP hQ,
  apply h,
  split,
  exact hP,
  exact hQ,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros h hPQ,
  cases hPQ with hP hQ,
    apply h,
    exact hP,
    exact hQ,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hP,
  exact hP,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hP,
  left,
  exact hP,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hQ,
  right,
  exact hQ,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro hPQ,
  cases hPQ with hP hQ,
    exact hP,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro hPQ,
  cases hPQ with hP hQ,
    exact hQ,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro hPP,
  cases hPP with hP,
    exact hP,
    intro hP,
    split,
    exact hP,
    exact hP,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro hPP,
  cases hPP with hP,
    exact hP,
    exact hPP,
    intro hP,
    left,
    exact hP,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q  : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro hnE,
  intro k,
  intro hP,
  apply hnE,
  existsi k,
  exact hP,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro hfAll,
  intro hE,
  cases hE with k hP,
    have hnPk : ¬P k := hfAll k,
      apply hnPk,
      exact hP,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro hnfAll,
  by_contra hnE,
    apply hnfAll,
    intro k,
  by_contra hnPk,
    apply hnE,
    existsi k,
  exact hnPk,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro hE,
  intro hnfAll,
  cases hE with k hnP,
    have hP : P k := hnfAll k,
      contradiction,

end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  apply demorgan_forall,
  apply demorgan_forall_converse,

end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  apply demorgan_exists,
  apply demorgan_exists_converse,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro hE,
  intro hnfAll,
  cases hE with k hP,
    have hnP : ¬P k := hnfAll k,
      contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro hfAll,
  intro hE,
  cases hE with k hnP,
    apply hnP,
    apply hfAll,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro hnE,
  intro k,
  by_contra hnP,
    apply hnE,
    existsi k,
    exact hnP,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intros hnfAll,
  by_contra hnE,
    apply hnfAll,
  intro k,
  intro hP,
  apply hnE,
  existsi k,
  exact hP,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  apply forall_as_neg_exists,
  apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall,
  apply exists_as_neg_forall_converse,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intros hEAnd,
  cases hEAnd with k hPQ,
    cases hPQ with hP hQ,
      split,
      existsi k,
      exact hP,
      existsi k,
      exact hQ,

end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intros hEOr,
  cases hEOr with k hPQ,
    cases hPQ with hP hQ,
      left,
      existsi k,
      exact hP,
    right,
    existsi k,
    exact hQ,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro hEOr,
  cases hEOr with hEP hEQ,
    cases hEP with k hP,
      existsi k,
      left,
      exact hP,
    cases hEQ with k hQ,
      existsi k,
      right,
      exact hQ,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro hfAll,
  split,
  intro k,
  have hPQ : P k ∧ Q k := hfAll k,
    cases hPQ with hP hQ,
    exact hP,
  intro k,
  have hPQ : P k ∧ Q k := hfAll k,
    cases hPQ with hP hQ,
    exact hQ,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro hfAllAnd,
  cases hfAllAnd with hfP hfQ,
    intro k,
    split,
    apply hfP,
    apply hfQ,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro hfAllOr,
  intro k,
  cases hfAllOr with hfP hfQ,
    left,
    apply hfP,
    right,
    apply hfQ,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate

