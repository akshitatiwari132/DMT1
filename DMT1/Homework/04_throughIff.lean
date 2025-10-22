/- @@@
#1. Suppose P and Q are any propositions.

#1.A: State and prove the conjecture that,
*and* implies *equivalence*. In other words,
if for any propositions, X and Y, X ∧ Y is
true, then it must be that X ↔ Y is as well.
Call your theorem andImpEquiv.
@@@ -/

theorem andImpEquiv (P Q : Prop) : P ∧ Q → (P ↔ Q) := -- for any props P and Q, if both P and Q are ture, then P and Q are equal
λ h =>Iff.intro -- (P → Q) → (Q → P) → (P ↔ Q), we have to assume h : P ∧ Q to prove what we want, -- we have to prove both sides - box that holds both directions(looking at inference rules in github)
  (λ hp => And.right h) -- we assume P is true, we used iff intro so we need to get the q, we need to prove P → Q
  (λ hq => And.left h) -- we assume Q is true, and now we need to do the Q → P version to return a proof of P


/- @@@
#2: Give the proof in #1 in English. To do this,
just explain clearly what assumptions you make or
use at each step and what inference rules you use
to make progress at each step. We get you started:

-- ANSWER
Proof: To prove this *implication* we'll use the
introduction rule for →. So *assume* the premise
is true. What remains to be proved is that, in this
context,  and we will then show that, in that
context, the conclusion must be true as well. So
assume P ∧ Q is true. The conclusion to be proved
is an equivalence. To prove an equivalence we need
to prove both ...

We basically first prove P → Q and then Q → P because
that's what the final proof is asking for, and we
use .left and .right to pull those parts out.
we used iffintro to combine the two parts there
for equivalence.


@@@ -/


/- @@@
#3: Use axiom declarations to represent this world.

- X is a proposition
- Y is a propostion
- X ∧ Y is true

Once you've done that, in a #check command, apply
the general theorem we just proved to prove that X
is equivalent to Y.

Do not just copy the proof. The whole point is to
reinforce the idea that one you've proved a theorem
you can use it (by applying it) to prove any special
case (here involving X and Y) of the general claim.
@@@ -/

-- Answer

axiom X : Prop -- we declare x is a prop
axiom Y : Prop -- we declare y is a prop
axiom XandY : X ∧ Y -- now we declare that its true

#check andImpEquiv X Y XandY -- yay!! it works


/- @@@
#4: Something About False

Recall from class discussion that the proposition,
in Lean, called False, has no proofs at all. That
is what makes it false. Assuming that there is one
assumes something that's impossibile. The crucial
conclusion to draw is *not* that the impossible is
suddenly possible, but that the *assumption* itself
must be wrong. Therefore, if at any point in trying
to prove something we can derive a proof of False,
that means we're in a situation that can't actually
happen. So we really don't have to finish the proof!

For example, suppose  K is some unknown proposition.
When we say that (False → K) is true, we are *not*
saying that *K* is true; we're saying that once you
assume or can derive a proof of False, you know you
are in a case that can never happen, so you can just
"bail out" and not worry about constructing a proof
of K, no matter what proposition it is. The keyword
*nomatch* in Lean applied to any proof of false does
exactly bail one of of an impossible case.

Here's a formal proof of it. We assume K is any
proposition, then we prove False → K. To prove
this implication, we assume we're given f, a proof
of false. In any other situation, for *exFalsoK*
to be defined, we'd *have to* return some value of
type K. Here we don't even know what that type is.
And yet the function is well-defined, and as such
*proves* the implication, *False → K*. The trick
of course, is that as soon as we have a proof of
false in (or derivable given) our context, then we
can *bail out* and Lean will accept the definition.
Lean's *nomatch* contruct will bail you out as long
as it's applied to a proof of false, which is the
evidence Lean needs to know it's ok to accept the
definition.
@@@ -/

theorem exFalseoK (K : Prop) : False → K := --for any prop k, if false is true then k is true, is defined as..
  λ f => nomatch f
-- given some input f, we need to assume false and prove k


/- @@@
Why is it safe to accept tihs definition? What do we
know that's special about *exFalsoK* that makes it ok?

ANSWER:

what's so special about exFalsoK is that false
is a false with no proofs. so the premise of the proof
which is false can never be fulfilled. therefore, we won't
ever have a real call to the function exFalseoK. that's why
we use nomatch, because f is a proof of something that
has no proofs, like what we talked about in class



@@@ -/


/- @@@
#5 In Lean, state and prove the proposition that is
P and Q are aribtrary propositions, then False *and*
P implies Q.
@@@-/

-- ANSWER

theorem falseaPimpQ (P Q : Prop) : False ∧ P → Q := -- for any 2 props P and Q, we're proving that false and P is true, implying Q is true
  λ h => nomatch (And.left h) -- assume we have h : False ∧ P, we take left side and take False, nomatch means case is impossible, so we're done


/- @@@
Write a short paragraph stating the proposition to be
proved and the proof of it -- in English.
@@@ -/

-- ANSWER
/-
this is telling us that for any two props P and Q,
if both False and P are true, then Q has to be true.
to prove this we are assuming we have False and P, and
we need to prove Q. We use elim on the left to extract the
False, now that we know this, we know false has no proofs,
so instead of acc doing it we use nomatch.

-/


/- @@@
#6 State and prove the proposition that False → False.
Give both formal and English (natural language) proofs.
@@@ -/

theorem falseimpfalse : False → False :=
  λ f => f -- given we know proof of false, we can return f which is already a proof of false

-- general q - how do u get the lambda symbol? i copy paste from other lean files
-- but wonder if there's an easier way?


-- ANSWER

/-
here we are saying that false implies false,
so assume we have false, then we just return itself
because false then false is valid even though false
can never be true. we basically just returned the
same thing

-/
