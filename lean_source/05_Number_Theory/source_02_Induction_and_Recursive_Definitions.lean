import data.nat.prime
import algebra.big_operators
import tactic.omega
import tactic

/- TEXT:
.. _section_induction_and_recursive_definitions:

Induction and Recursive Definitions
-----------------------------------

The set of natural numbers, :math:`\mathbb{N} = \{ 0, 1, 2, \ldots \}`,
is fundamentally important in its own right and is a basic component
of many mathematical constructions.
In Lean, the natural numbers are given axiomatically, as part
of the logical foundation,
via the following declaration.
OMIT:-/
namespace hidden
-- QUOTE:
inductive nat
| zero : nat
| succ (n : nat) : nat
-- QUOTE.
end hidden

/- TEXT:
You can find it in the library by writting ``#check nat`` and
then using ``ctrl-click`` on the identifier ``nat``.
The command specifies that ``nat`` is the datatype generated
freely and inductively by the two *constructors*, ``zero : nat`` and
``succ : nat → nat``.
What "freely" means for the working mathematician is that the type
``nat`` has an element ``zero`` and an injective successor function
``succ`` whose image does not include ``zero``.
EXAMPLES: -/
example (n : nat) : n.succ ≠ nat.zero := nat.succ_ne_zero n

example (m n : nat) (h : m.succ = n.succ) : m = n :=
nat.succ.inj h

/- TEXT:
Of course, the library introduces notation ``ℕ`` and ``0`` for
``nat`` and ``zero`` respectively. (Numerals are translated to binary
representations that we don't have to worry about now.)

What the word "inductively" means for the working mathematician is that
the natural numbers comes with a principle of proof by induction
and a principle of definition by recursion.
The goal of the section is to show you how to use these.

Here is an example of a recursive definition of the factorial
function.
EXAMPLES: -/
-- QUOTE:
def fac : ℕ → ℕ
| 0 := 1
| (n + 1) := (n + 1) * fac n
-- QUOTE.

/- TEXT:
The syntax takes some getting used to.
Notice that there is no ``:=`` on the first line.
The next two lines provide the base case and inductive step
for a recursive definition.
These equations hold definitionally, but they can also
be used manually by giving the name ``fac`` to ``simp`` or ``rw``.
EXAMPLES: -/
-- QUOTE:
example : fac 0 = 1 := rfl
example : fac 0 = 1 := by rw fac
example : fac 0 = 1 := by simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := rfl
example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by rw fac
example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by simp [fac]
-- QUOTE.

/- TEXT:
In fact, the factorial function is defined in mathlib as
``nat.factorial``. Once again, you can jump to it by typing
``#check nat.factorial`` and using ``ctrl-click.``
For illustrative purposes, we will continue using ``fac`` in the examples.
The annotation ``@[simp]`` before the definition
of ``nat.factorial`` specifies that
the defining equation should be added to the database of identities
that the simplifier uses by default.

The principle of induction also reflects the definition of the
natural numbers. The line ``induction n with n ih`` in the proof
below results in two goals.
In the first we need to prove ``0 < fac 0``,
and in the second we have the added assumption ``ih : 0 < fac n``
and a required to prove ``0 < fac (n + 1)``.
The phrase ``with n ih`` serves to name the variable and
the assumption for the inductive hypothesis,
and these can be arbitrary.
EXAMPLES: -/
-- QUOTE:
theorem fac_pos (n : ℕ) : 0 < fac n :=
begin
  induction n with n ih,
  { rw fac, apply zero_lt_one },
  rw fac,
  exact mul_pos n.succ_pos ih,
end
-- QUOTE.

/- TEXT:
The ``induction`` tactic is smart enough to include hypotheses
that depend on the induction variable.
Here's another example. Step through it to see what is going on.
EXAMPLE: -/
theorem dvd_fac_of_le {i n : ℕ} (h : i ≤ n) (h' : i ≠ 0) :
  i ∣ fac n :=
begin
  induction n with n ih,
  { rw nat.le_zero_iff at h, contradiction },
  rw fac,
  cases nat.of_le_succ h with h'' h'',
  { apply dvd_mul_of_dvd_right (ih h'')},
  rw h'',
  apply dvd_mul_right
end

/- TEXT:
The following example provides a crude lower bound for the factorial
function.
It turns out to be easier to start with a proof by cases,
so that the remainder of the proof starts with the case
:math:`n = 1`.
See if you can fill that in with a proof by induction.
BOTH: -/
theorem pow_two_le_fact (n : ℕ) : 2^(n-1) ≤ fac n :=
begin
  cases n with n,
  { simp [fac] },
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction n with n ih,
  { simp [fac] },
  simp at *,
  rw [pow_succ, fac],
  apply nat.mul_le_mul _ ih,
  repeat { apply nat.succ_le_succ },
  apply zero_le
-- BOTH:
end

/- TEXT:
Induction is often used to prove identities involving finite sums and
products.
Mathlib defines the expressions ``finset.sum s f`` where
``s : finset α`` if a finite set of elements of the type ``α`` and
``f`` is a function defined on ``α``.
The codomain of ``f`` can be any type that supports a commutative,
associative addition operation with a zero element.
If you import ``algebra.big_operators`` and issue the command
``open_local big_operators``, you can use the more suggestive notation
``∑ x in s, f x``. Of course, there is are an analogous operation and
notation for finite products.

We will talk about the ``finset`` type and the operations
it supports in a later chapter. For now, we will only make use
of ``finset.range n``, which is the finite set of natural numbers
less than ``n``.
EXAMPLES: -/
section

-- QUOTE:
variables {α : Type*} (s : finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check finset.sum s f
#check finset.prod s f

open_locale big_operators

example : s.sum f = ∑ x in s, f x := rfl
example : s.prod f = ∏ x in s, f x := rfl

open finset

example : (range n).sum f = ∑ x in range n, f x := rfl
example : (range n).prod f = ∏ x in range n, f x := rfl
-- QUOTE.

/- TEXT:
The facts ``finset.sum_range_zero`` and ``finset.sum_range_succ``
provide a recursive description of the values, and
similarly for products.
EXAMPLES: -/
example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ):
  ∑ x in range n.succ, f x = (∑ x in range n, f x) + f n :=
finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ):
  ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
finset.prod_range_succ f n
-- QUOTE.

/- TEXT:
In fact, the first identity in each pair holds definitionally.

The following expresses the factorial function that we defined as a product.
The first command turns off a simplification rule that would rewrite
the product to ``nat.factorial``.
EXAMPLES: -/
local attribute [-simp] prod_range_add_one_eq_factorial

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) :=
begin
  induction n with n ih,
  { simp [fac] },
  simp [fac, ih, prod_range_succ, mul_comm]
end

/- TEXT:
The fact that we include ``mul_comm`` as a simplification rule deserves
comment.
It should seem dangerous to simplify with the identity ``x * y = y * x``,
which should ordinarily loop indefinitely.
Lean's simplifier is smart enough to recognize that, and applies the rule
only in the case where the resulting term has a smaller value in some
fixed but arbitrary ordering of the terms.
The following example shows that simplifying using the three rules
``mul_assoc``, ``mul_comm``, and ``mul_left_comm``
has the net effect of putting terms in a canonical form.
EXAMPLE: -/
-- QUOTE:
example (a b c d e f : ℕ) :
  a * ((b * c) * f * (d * e)) = d * (a * f * e) * (c * b) :=
by simp [mul_assoc, mul_comm, mul_left_comm]
-- QUOTE.

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 :=
begin
  symmetry, apply nat.div_eq_of_eq_mul_right,
  { by norm_num },
  induction n with n ih,
  { simp },
  rw [finset.sum_range_succ, mul_add 2, ←ih, nat.succ_eq_add_one],
  ring
end

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i^2 = n * (n + 1) * (2 *n + 1) / 6 :=
begin
  symmetry, apply nat.div_eq_of_eq_mul_right,
  { by norm_num },
  induction n with n ih,
  { simp },
  rw [finset.sum_range_succ, mul_add 6, ←ih, nat.succ_eq_add_one],
  ring
end


example {m : ℕ} (h : m < 2) : m = 0 ∨ m = 1 :=
by dec_trivial!

theorem exists_prime_factor {n : nat} (h : 2 ≤ n) :
  ∃ p : nat, p.prime ∧ p ∣ n :=
begin
  by_cases np : n.prime,
  { use [n, np, dvd_rfl] },
  induction n using nat.strong_induction_on with n ih,
  dsimp at ih,
  rw nat.prime_def_lt at np,
  push_neg at np,
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩,
  have : m ≠ 0,
  { intro mz, rw [mz, zero_dvd_iff] at mdvdn, linarith },
  have mgt2 : 2 ≤ m,
  -- { by_contradiction hm, push_neg at hm, interval_cases m; contradiction },
  { omega },
  by_cases mp : m.prime,
  { use [m, mp, mdvdn] },
  rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩,
  use [p, pp, pdvd.trans mdvdn]
end

theorem primes_infinite : ∀ n, ∃ p > n, nat.prime p :=
begin
  intro n,
  have : 2 ≤ fac (n + 1) + 1,
  { apply nat.succ_le_succ,
    exact nat.succ_le_of_lt (fac_pos _) },
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩,
  refine ⟨p, _, pp⟩,
  show p > n,
  by_contradiction ple, push_neg at ple,
  have : p ∣ fac (n + 1),
  { apply dvd_fac_of_le,
    linarith,
    apply pp.ne_zero },
  have : p ∣ 1,
  { convert nat.dvd_sub' pdvd this, simp },
  have := nat.le_of_dvd zero_lt_one this,
  linarith [pp.two_le]
end

theorem foo (m n : ℕ) (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 :=
begin
  revert h,
  rw [nat.mul_mod],
  have : m % 4 < 4 := nat.mod_lt m (by norm_num),
  interval_cases m % 4 with hm; simp [hm],
  have : n % 4 < 4 := nat.mod_lt n (by norm_num),
  interval_cases n % 4 with hn; simp [hn]; norm_num
end





-- later
-- fibonacci numbers
-- binomial coefficients


-- OMIT

/-
This was false... but we need to mention ``local attribute`` at some point.

We can also add the equations after the fact,
in our case,
with the command ``attribute [simp] fac``.
If instead we write ``local attribute [simp] fac``,
the equations are added only within the current section or file.
-/