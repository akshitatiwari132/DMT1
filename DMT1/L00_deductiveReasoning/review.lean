-- if p and p are true, we know p is true P ∧ P <-> P (<-> = equivalent)
-- if p or p is true, we know p is true P ∨ P <-> P
-- T (top) = true
-- upside down T (bottom) = false
-- P or true is equivalent to p --> we should be able to come up w a counterexample if its false (it is) , counterexample is P = false (upside down T)
-- P or false is equivalent to p --> works both directions all the time
-- (P ∨ Q) ∨ R <-> P ∨ (Q ∧ R) --> disjunctions on both sides, left side is either p or q is true or r is true
-- 30 boolean variables - 2^30 possible states - billion
-- 32 bits in java
-- 32 bit means 4 billion possible states



-- (P -> Q) -> (not P -> not Q) -- NOT A VALID one in propositional logic bc not true in all worlds
-- streets can be wet without rain , not a valid proposition
-- if whenever its raining streets are wet


-- demorgans law - if its not the case that p and q are both true, it must be that one of them is not true

-- she ate a donut or she ate a candy bar AND she ate a candy bar, can u conclude she didnt eat a donut? from p or q AND p, can u deduce not q?
--


example { P Q : Prop } : ¬(P ∧ Q) : ¬(P ∧ Q) → ¬P ∨ ¬ Q :=
(
  fun (h : ¬(P ∧ Q)) => _
)
-- lean is less than traditional logic

axiom em : ∀ P : Prop, P ∨ ¬P

example { P Q : Prop } : ¬(P ∧ Q) → ¬P ∨ ¬Q :=
(
  fun (h : ¬(P ∧ Q)) =>
  let pornp := em P
  match pornp with
  | Or.inl p => match (em Q) with
    | Or.inl q => False.elim (h (And.intro p q))
    | Or.inl nq => Or.inr nq
  | Or.inr np => Or.inl np
)

-- on assumption p and q arent true, this is a case that cant happen
-- STUDY
