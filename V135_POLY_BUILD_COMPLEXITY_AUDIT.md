# TCS #1 v135 — `thm:poly-build` complexity audit (2026-10-10)

> Manuscript `Papers/01_fixed-h-cfg/main.tex` v135 (sha256 `e8590799…`), `thm:poly-build`:
> *For fixed `h`, `B_h(K)` is constructible in time polynomial in `‖K‖`.*  The proof sketches an
> `O(n_K^4)` bound (`n_K = ‖K‖`), ending with: "Even if factor strings are written literally in
> productions, each production has encoding length `O(n_K)`, so the grammar can be checked and
> written explicitly in `O(n_K^4)` time."
>
> CI status of the files below: see the top section of `NEXT_CHAT_HANDOFF_TCS1_2026-10-10.md`.

## 1. What was implemented

| File | Content |
|---|---|
| `V135CostedPrimitives.lean` | step-counted primitives (`lengthC`, `dropC`, `takeC`, `sliceC`, `eqC`, `typeC`) and loop combinators (`forNatC`, `forListC`); value lemmas and step bounds |
| `V135PolyBuildAlgorithm.lean` | the constructor `constructV116C`, exactness of every output component against self-contained specifications, and `constructV116Cost_le` |
| `V135PolyBuildBridge.lean` | connection with the verified v116 tables and `BatchLanguage`; paper-facing `thm_polyBuild` |

**Constructor.** Input: a list `ws` of sample words (any listing of `K`). Output: a `V116GrammarCode`
(lists of nonterminals and of (B), (U), (L), (S) productions and an ε flag). Nonterminals are written
**literally as factor strings**, as the manuscript allows. Equal names are equal strings, so no
hashing, fingerprinting or identifier assignment occurs, and string equality never needs to be
"assumed" constant time. Productions may be repeated in the output lists; the *set* of productions
is the v116 grammar (duplicate elimination is not performed — see §6).

* (B): for every `w ∈ ws` and `0 ≤ i < j < k ≤ |w|`, emit `w[i:k] → w[i:j] w[j:k]`.
* (U): for every ordered pair `w, w' ∈ ws`, every `i`, every `j ≤ |w|` and `j' ≤ |w'|` with `i < j`, `i < j'`:
  compare the left contexts `w[0:i]`, `w'[0:i]` letter by letter, compare the right contexts
  `w[j:]`, `w'[j':]` letter by letter, compute both `h`-types letter by letter, and emit
  `w[i:j] → w'[i:j']` iff all three agree.
* (L): every one-letter factor `w[i:i+1] = [a]` gives `[a] → a`.
* (S): every nonempty `w ∈ ws`. (ε): flag iff `[] ∈ ws`.
* Nonterminals: every nonempty factor `w[i:j]`.

## 2. Semantic correctness (Theorems A, B)

* `mem_binary`, `mem_unary`, `mem_lexical`, `mem_start`, `epsilon_iff`, `mem_nonterminals`
  (algorithm file): exact characterizations in terms of occurrences `p ++ x ++ q ∈ ws`.
* Bridge (`K = ws.toFinset`): `constructV116H_binary_iff` (= `v116EffectiveBinaryWordTable K`, and via
  `v116EffectiveBinaryWordTable_eq_actual` the actual (B) table), `constructV116H_unary_iff`
  (= `v116UnaryRuleTable H K`), `constructV116H_lexical_iff`, `constructV116H_start_iff`,
  `constructV116H_epsilon_iff`, `constructV116H_nonterminals_iff`.
* `constructV116H_language`: the grammar *as written*, read as a CFG over its literal names
  (`codeGrammar`, `codeLanguage`), generates exactly `BatchLanguage H K`. The proof transfers
  derivations to and from the verified `finiteSubstringGrammar` and uses
  `finiteSubstringBatchLanguage_eq_batchLanguage`.

Edge cases are covered by the general theorems: the empty sample, `λ ∈ K` (ε flag only, no ε rule on
non-start nonterminals), repeated factor occurrences (repeated output rows, same set), and the same
factor in several sample words.

## 3. Cost model (fixed before the proofs)

All functions return `(value, steps)`; the step count is produced **by the same recursion** that
computes the value (no separate cost function). One step is charged for:

* visiting or creating one linked-list cell (so `drop`, `take`, `length`, word comparison, and the
  spine copy of every output append are charged per cell);
* one equality test of two letters (`DecidableEq α`; fixed alphabet);
* one letter-type lookup `h(a)` and one multiplication in the fixed finite monoid, and one
  equality test of two monoid elements (`DecidableEq M`; fixed finite monoid);
* one comparison of two loop indices (natural numbers bounded by the input length; word-RAM unit
  cost — this is an operation count, not bit complexity);
* one unit of loop overhead per iteration.

Not used by the algorithm: `Finset` operations, hashing, sorting, arrays. No unbounded operation is
treated as constant time.

## 4. Operation counts (all proved, `a = |w|+1`, `b = |w'|+1`, `N = Σ_{w∈ws}(|w|+1)`)

| Stage | Per item | Lemma | Total |
|---|---|---|---|
| nonterminal listing | `≤ 19 a³` per word | `ntWord_bound` | `≤ 38 N³ + N + 1` |
| (B) | body `≤ 7a`; word `≤ 71 a⁴` | `binaryBody_bound`, `binaryWord_bound` | `≤ 142 N⁴ + N + 1` |
| (U) | body `≤ 15(a+b)` (two takes, two drops, two comparisons, two slices, two typings); pair `≤ 135 a²b(a+b)` | `unaryBody_bound`, `unaryPair_bound` | `≤ 1084 N⁴ + N + 1` |
| (L) | `≤ 11 a²` per word | `lexicalWord_bound` | `≤ 22 N² + N + 1` |
| (S), (ε) | 1 per word | — | `≤ 3N + 1` each |
| **whole constructor** | | `constructV116Cost_le` | **`≤ 1400 · (N + 1)^4`** |

`thm_polyBuild` / `constructV116HCost_le`: for a duplicate-free listing of `K`, `N = ‖K‖`, hence
**`T_construct(K) ≤ 1400 · (‖K‖ + 1)^4`**. The constant is an absolute numeral: it does not depend
on `h`, `Σ` or `M`, because letter tests, letter-type lookups and monoid operations are unit-cost
in the model.

## 5. Agreement with the manuscript

* Theorem statement ("time polynomial in `‖K‖`"): **proved** for the cost model of §3, for the
  manuscript's operator (`B_h(K)` in its v116 form), with explicit quartic polynomial.
* Proof sketch's `O(n_K^4)`: **proved** in the same model. The verified algorithm differs from the
  sketch in its accounting:
  - (U) is enumerated over pairs of occurrences with literal context comparison
    (`O(n_K³)` iterations × `O(n_K)` per iteration), instead of bucket grouping with canonical
    identifiers;
  - no canonical identifiers are computed;
  - output rows may repeat.

  The quartic bound therefore does not depend on the manuscript's "after preprocessing … constant
  time" step. No change to the manuscript is required. One could optionally note that bucket
  grouping is not needed for the quartic bound.
* `thm:main`(i) ("`B_h(K)` constructible in time polynomial in `‖K‖`") is now backed by this
  theorem for the v116 operator. `thm:main`(iii)'s per-update bound remains the v79 materialized
  learner accounting (a different, extensionally equal representation).

## 6. Not accounted / out of scope

* **Duplicate elimination** of repeated productions is not performed. Producing a duplicate-free
  list would need extra work (e.g. sorting); not claimed.
* **Machine model:** the count is a RAM/pointer-machine operation count. It is not a semantics of
  compiled Lean code, and not bit complexity. Unit cost of monoid operations relies on `M` being
  fixed and finite.
* **Input format:** a list of words. `‖K‖` equals the list norm when the list has no repetitions
  (`inputNorm_eq_sampleNorm`). A list with repetitions is charged by its own length.
* **Learner updates:** the per-update cost of the sequential learner is not re-derived for the v116
  representation.
