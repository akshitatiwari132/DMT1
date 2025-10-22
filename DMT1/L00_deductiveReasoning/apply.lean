-- def a fn called apply 0
-- assume α : Type (implicit)
-- assume f : α → α
-- goal : value of f applied 0 times to its alignment

def apply0 {α : Type} : (α → α) → α → α
| f, a → a
| f, a → (f a) =>

def two {α : Type} : (α → α) → (a : α) → α
| f, a => f (f a)

def three {α : Type} : (α → α) → (a : α) → α
| f, a => f (f (f a))

def four {α : Type} : (α → α) → (a : α) → α
| f, a => f (f (f (f a)))

-- function compose takes and returns output, circle operator is composition

#check three
#check (@three Nat)

#reduce @two Nat

-- composition takes input, output, feeds it into another function
-- if u look at two

def inc (n : Nat) := n + 1 -- now lets take output of this and feed into 3
#eval two inc 8
#eval two inc 0
#eval three inc (two inc 0)
#reduce ((@two Nat) ∘ (@three Nat))

-- u can take tiny piece of math and can represent truth values as functions (looking back to hw3)
-- implemented if this then that else something else
-- takes either true func or false and 2 more arguments, if rep of boolean is true, applies that to remaining arguments to return first
-- otherwise applies false and returns second
-- now represented booleans as functions
-- THIS IS lambda calculus

#reduce ((@two Nat) ∘ (@three Nat))
#eval four inc (three inc 0)


def whatIsThis := ((@three Nat) ∘ (@four Nat))

#reduce whatIsThis


/-
representing natural numbers as iterated function application and addition then as composition
of these functions
-/


-- what do u do if u want proof of p for p? construct proof of implications
-- if p is true, we show p is true. so we need to assume premise is true, that theres a proof of p
-- so we need to return p
-- if theres a proof of p, then theres a proof of p

theorem refl {P : Prop} : P → P := (fun p => p)
-- a proof of implication is a function
-- we specify functions using lambda abstractions (starting w/ fun)
-- funny arrow then result

-- light is on if power is on, power has to be on if light is on
-- if light is off, power must be off

