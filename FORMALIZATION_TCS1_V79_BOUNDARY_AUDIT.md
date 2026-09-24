# TCS #1 v79 boundary audit

This note records the final review of manuscript statements that are **not**
intended to become internal Lean proof obligations.

Manuscript baseline:

- source: `TCS-D-26-00494_major_revision_working_v79(1)(1).tex`;
- SHA-256:
  `3d54aaea1c945e4b9bbdabe92a88f229096d94c93fa3045a3bfda5dfd22426d2`.

The purpose is to distinguish a genuine formalization gap from one of three
legitimate boundaries:

1. cited literature/background;
2. an explicit representation convention;
3. a statement that the paper itself leaves open.

A statement appears below only if it was rechecked against the current v79
source rather than being silently treated as background.

---

## A. Gold's negative theorem and the superfinite union class

**Manuscript:** lines 43--45 and 260--266.

**Decision:** mixed internal/external boundary; no paper-specific gap.

Internally verified:

- `regular_auto_proposition_package` gives the finite-automaton /
  finite-monoid recognition equivalence used by Proposition 3.1;
- `regular_exists_fixedHSubstitutable` states directly that every regular
  language belongs to at least one fixed-h substitutable class;
- `goldThreeWordSample_not_fixedH` and
  `fixedH_omits_some_finite_language` verify the separate post-Theorem 3.4
  point that a *fixed* `RS_h` need not contain all finite languages.

Kept external:

- Gold's theorem that every superfinite class fails positive-data
  identification in the limit;
- the standard automata fact that every finite language is regular.

The manuscript cites Gold for the negative theorem.  Re-proving Gold's
general theorem would be a separate formal-learning-theory project and is not
needed for the fixed-h positive result.

---

## B. Historical distributional-learning results

**Manuscript:** lines 47--55, 109--115, and 936--940.

**Decision:** keep as cited literature/background.

This includes:

- Clark--Eyraud substitutability;
- Yoshinaka's fixed-window learnability theorem and the historical
  grammar-size/thickness comparison;
- Kanazawa's positive-data results for restricted categorial grammars.

The present development verifies its own fixed-window equivalence,
normalization, witness bounds, and characteristic-data polynomial.  The
phrase that the bound has the "same ... scale established by Yoshinaka" is a
cross-paper comparison, not an internal dependency.  Formalizing Yoshinaka's
entire earlier proof would not strengthen the correctness of the current
paper's own theorem.

---

## C. Typing/domain-bias and control-set positioning

**Manuscript:** lines 84--96.

**Decision:** keep as cited positioning/background.

The comparison with automata-inference typing/domain bias and the contrast
with Takada/control-set approaches are explicitly used only for positioning.
The manuscript itself says that no class separation from the full control-set
framework is claimed.

No current theorem depends on these historical comparisons.

---

## D. "Reasonable encoding" convention

**Manuscript:** lines 180--183; used again implicitly in Appendix A around
lines 1598--1612.

**Decision:** keep as an explicit representation convention.

The manuscript writes `|r|` for a fixed reasonable encoding and notes that,
for grammars, this is polynomially equivalent to ordinary production-symbol
count.

The Lean development instead proves explicit combinatorial bounds on:

- finite state spaces;
- candidate production spaces;
- stored production tables;
- symbol/output envelopes;
- finite scan/comparison work.

Thus the formal complexity results do not silently assume a particular byte
serialization.  A metatheorem quantifying over *all reasonable encodings*
would require first formalizing a class of encodings and a notion of
reasonable polynomial equivalence, which is intentionally outside the
paper's abstraction level.

---

## E. One-turn pushdown characterization of linear languages

**Manuscript:** lines 945--948.

**Decision:** keep as cited literature/background.

The sentence "Linear languages are exactly the languages accepted by
one-turn pushdown automata" is used to motivate the term
"linear-spine"; it is not used in the proof of Proposition 8.1 or Theorem
8.3.

Internally verified instead are the grammar-theoretic claims actually needed:

- `indexedLinear_normalization_source_package`;
- `indexedLinear_normalization_shape`;
- `indexedLinear_normalization_size_le`;
- `indexedLinear_characteristic_package`.

There is no general PDA library in the current TCS1 development, so importing
a full one-turn-PDA equivalence proof solely for this motivational sentence
would add substantial unrelated infrastructure.

---

## F. Deterministic-context-free status of the Section 9 examples

**Manuscript:** lines 1336--1338, 1358, 1369--1380, and 1393--1399.

**Decision:** keep the deterministic-PDA/DCFL classification as
literature/background; keep the new RS obstructions internal.

Internally verified:

- `finiteMonoid_obstruction`;
- `finiteMonoid_obstruction_uniform`;
- `UncappedCounter.not_fixedH`;
- `DyckOne.not_fixedH`;
- `fixedHSubstitutable_fixedRightQuotient`;
- the Dyck/Clark comparison package used later in Proposition 9.9.

Kept external/cited:

- the standard deterministic pushdown characterization of the uncapped
  counter language;
- the standard deterministic-context-free status of the one-bracket Dyck
  language;
- the standard deterministic-context-free status of the Lukasiewicz
  language;
- the classical identity `L_Luk = D_1 b` under the manuscript's coding.

The paper's original contribution here is the fixed-finite-monoid
obstruction, not a new proof that these classical languages are DCFLs.
Consequently the statement "RS does not contain all deterministic
context-free languages" uses a standard cited classification together with a
fully internal RS-exclusion proof.

---

## G. Expository batch-syntax observation

**Manuscript:** lines 550--554.

**Decision:** promoted to Lean-internal representation evidence.

The paper notes that the raw batch operator need not stabilize syntactically
when recomputed after every newly observed positive example.  Rather than
formalizing the specific `a^n c b^n` text from the footnote, the repository
now proves the stronger generic representation fact:

- `reconstructionFactorSlotCount_insert`;
- `reconstructionFactorSlot_card_lt_insert`.

Whenever a genuinely new sample word is inserted, the occurrence-indexed
factor/context state universe used by the executable batch grammar grows
strictly.  This is exactly the syntactic phenomenon for which the paper
introduces the conservative sequential wrapper.  No language-semantic theorem
depends on this observation.

---

## H. Open problems in the Conclusion

**Manuscript:** lines 1491--1497.

**Decision:** explicitly open; never a Lean proof obligation.

The manuscript leaves open:

- a complete characterization of `RS ∩ CFL`;
- criteria for useful finite typings;
- learning when `h` is unknown;
- extensions to richer grammar formalisms;
- a polynomial characteristic-data bound in grammar size and thickness for
  arbitrary fixed-h general CFG presentations.

The audit must not turn any of these into an asserted theorem.

---

## I. Final boundary decision

After this review, no remaining item classified as
literature/background, convention, or open problem is being used to hide a
known gap in the paper's *new* mathematical arguments.

The one borderline Section 3 claim that previously deserved stronger
internal treatment -- strictness of the syntactic-kernel refinement
criterion -- has now been promoted into Lean via:

- `isRegular_of_fixedH_type_refines_distribution`;
- `nonregular_has_same_type_distinct_distribution`;
- `lpm_fixedH_without_syntactic_kernel_refinement`.

Likewise, the regular-to-union-class step is now explicit via
`regular_exists_fixedHSubstitutable`.

The remaining external boundary is therefore narrow and conventional:
classical cited theorems, historical comparisons, one encoding convention,
and questions explicitly stated as open by the manuscript.
