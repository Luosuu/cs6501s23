import analysis.normed_space.finite_dimension
import analysis.convolution
import measure_theory.function.jacobian
import measure_theory.integral.bochner
import measure_theory.measure.lebesgue

open set filter
open_locale topological_space filter ennreal
noncomputable theory

/- TEXT:
.. index:: measure theory

.. _measure_theory:

Measure Theory
--------------

The general context for integration in mathlib is measure theory. Even the elementary
integrals of the previous section are in fact Bochner integrals. Bochner integration is
a generalization of Lebesgue integration where the target space can be any Banach space,
not necessarily finite dimensional.

The first component in the development of measure theory
is the notion of a :math:`\sigma`-algebra of sets, which are called the
*measurable* sets.
The type class ``measurable_space`` serves to equip a type with such a structure.
The sets ``empty`` and ``univ`` are measurable,
the complement of a measurable set is measurable,
and a countable union or intersection of measurable sets is measurable.
Note that these axioms are redundant; if you ``#print measurable_space``,
you will see the ones that mathlib uses.
As the examples below show, countability assumptions can be expressed using the
``encodable`` type class.
BOTH: -/
-- QUOTE:
variables {α : Type*} [measurable_space α]

-- EXAMPLES:
example : measurable_set (∅ : set α) := measurable_set.empty

example : measurable_set (univ : set α) := measurable_set.univ

example {s : set α} (hs : measurable_set s) : measurable_set sᶜ :=
hs.compl

example : encodable ℕ :=
by apply_instance

example (n : ℕ) : encodable (fin n) :=
by apply_instance

-- BOTH:
variables {ι : Type*} [encodable ι]

-- EXAMPLES:
example {f : ι → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋃ b, f b) :=
measurable_set.Union h

example {f : ι → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋂ b, f b) :=
measurable_set.Inter h
-- QUOTE.

/- TEXT:
Once a type is measurable, we can measure it. On paper, a measure on a set
(or type) equipped with a
:math:`\sigma`-algebra is a function from the measurable sets to
the extended non-negative reals that is
additive on countable disjoint unions.
In mathlib, we don't want to carry around measurability assumptions
every time we write an application of the measure to a set.
So we extend the measure to any set ``s``
as the infimum of measures of measurable sets containing ``s``.
Of course, many lemmas still require
measurability assumptions, but not all.
BOTH: -/
-- QUOTE:
open measure_theory

variables {μ : measure α}

-- EXAMPLES:
example (s : set α) : μ s = ⨅ t (st : s ⊆ t) (ht : measurable_set t), μ t :=
measure_eq_infi s

example  (s : ι → set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
measure_Union_le s

example {f : ℕ → set α}
    (hmeas : ∀ i, measurable_set (f i)) (hdis : pairwise (disjoint on f)) :
  μ (⋃ i, f i) = ∑' i, μ (f i) :=
μ.m_Union hmeas hdis
-- QUOTE.

/- TEXT:
Once a type has a measure associated with it, we say that a property ``P``
holds *almost everywhere* if the set of elements where the property fails
has measure 0.
The collection of properties that hold almost everywhere form a filter,
but mathlib introduces special notation for saying that a property holds
almost everywhere.
EXAMPLES: -/
-- QUOTE:
example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in μ.ae, P x :=
iff.rfl
-- QUOTE.
