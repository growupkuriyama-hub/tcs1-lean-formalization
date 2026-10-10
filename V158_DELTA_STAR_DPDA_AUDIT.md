# TCS #1 v158 — `prop:nonlinear-rs-example`: the DCFL clause by an explicit DPDA (2026-10-10)

> **Manuscript.** `Papers/01_fixed-h-cfg/main.tex` **v158** (`044c5ce`, sha256 `bb5a334c4a313b3e3b4ce9ef9ea9686fc08e52e8a911e5510c937015eaed7138`). The statement of `prop:nonlinear-rs-example` is unchanged since v135. Its proof was rewritten in v143–v156 (admissible entry heights `Q(x)`, (⋆), (⋆⋆)).
> **CI.** New V158 theorems verified in CI #1044 (`5207728`, DPDA), CI #1048 (`783bf83`, CYK and learner) and `d95c5af0c6e672cb65214e8760a3e2ff39ace387` — [CI #1050](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38053099704) SUCCESS (all 5 gates, including the V158 `#guard_msgs` axiom audit). `V158ObstructionSet` was added in the final commit.

## 1. Gap before this session

The Lean package `DeltaStar.nonlinear_rs_example_full` proved every clause except "**deterministic context-free**". The repository had a deterministic *membership function* (`DeltaStar.scan`), but no pushdown-automaton model. A decision procedure is not a DCFL proof, so the clause was graded **P**.

## 2. General DPDA model — `V158DPDA.lean`

Neither Mathlib nor the repository has pushdown automata, so the standard definition is formalized here:

```lean
structure DPDA (Q : Type u) (Γ : Type v) (σ : Type w) where
  start : Q
  bottom : Γ
  final : Q → Prop
  trans : Q → Option σ → Γ → Option (Q × List Γ)          -- none = ε-move
  det : ∀ q Z, (trans q none Z).isSome → ∀ a, trans q (some a) Z = none
```

* Configurations are `(state, unread input, stack)`. `Step` has a reading move and an ε-move. `Reaches` is the reflexive–transitive closure (`Relation.ReflTransGen`). `Accepts w` holds iff `(start, w, [bottom]) ⊢* (q, [], st)` with `final q`, i.e. acceptance by final state.
* `DPDA.step_deterministic`: the one-step relation is functional. It depends on **no axioms**.
* `RealTime M` (no ε-moves), `run`, `reaches_iff_run`, `accepts_iff_run`: for real-time DPDAs, acceptance equals a deterministic run.
* `IsDCFL L := ∃ (Q Γ : Type) (_ : Fintype Q) (_ : Fintype Γ) (M : DPDA Q Γ σ), M.language = L`.
  - Finite control and finite stack alphabet are required.
  - This is **not** a decidability predicate.

## 3. The DPDA for `Δ*` — `V158DeltaStarDPDA.lean`

| component | value |
|---|---|
| states | `ready` (final), `up`, `down` |
| stack alphabet | `bot` (initial), `first` (cell of the first `a` of a block), `mark` (further `a`s) |
| moves | `ready,a,bot ↦ up,[first,bot]`; `up,a,first ↦ up,[mark,first]`; `up,a,mark ↦ up,[mark,mark]`; `up/down,b,mark ↦ down,[]`; `up/down,b,first ↦ ready,[]` |
| undefined (reject) | `b` on `bot` (empty stack); `a` while in `down` (an unfinished `b`-part) |
| ε-moves | none (real-time) |

The separate `first` cell tells the finite control that the stack has returned to the bottom marker. This makes acceptance by the final state `ready` exact, matching the manuscript's "permits a new such factor only after the stack returns to its bottom marker".

Theorems (requested items A–E):

| | theorem | content |
|---|---|---|
| A | `deltaStarDPDA_realTime`, `DPDA.step_deterministic` | determinism, no ε-moves |
| B | `stack_length_eq` | after reading a prefix `u`, the stack length is `1 + (|u|_a − |u|_b)`: the bottom marker plus the unmatched `a`s |
| C | `run_encode`, `deltaStarDPDA_accepts_iff_scan` | the DPDA run simulates the existing parser `scan` step by step; DPDA acceptance ⇔ `scan .zero w = some .zero` |
| D | `deltaStarDPDA_language`, `deltaStarDPDA_language_eq_star`, `deltaStarDPDA_language_eq_displayed` | `L(DPDA) = DeltaStar.Language` = Kleene star of the blocks `aⁿbⁿ` (`StarDerives`) = the language of the displayed grammar `S → TS | λ, T → aTb | λ` (`SDerives`) |
| E | `deltaStar_isDCFL` | `IsDCFL DeltaStar.Language` |

Paper-facing: `DeltaStar.nonlinear_rs_example_full_dcfl` (`V158DeltaStarDCFLPackage.lean`) contains every clause of the manuscript statement:
- DCFL, with the DPDA language equal to the block star;
- the displayed CFG and the finite binary CFG;
- nonregular;
- nonlinear (`¬ RawLinearInitialRepresentable`);
- `FixedHSubstitutable starTyping`;
- outside every fixed window.

## 4. Additional DCFL remarks — `V158CounterDyckDPDA.lean`

The manuscript calls `CTR` "accepted by the evident deterministic pushdown counter with reset", and `D₁` "a standard deterministic context-free language". These are prose remarks, not numbered claims. With the same model:
- `UncappedCounter.uncappedCounter_isDCFL`: one state; `reset` pushes a fresh bottom marker; underflow is an undefined move.
- `DyckOne.dyckOne_isDCFL`.

## 5. Audit of the v143–v158 proof of `prop:nonlinear-rs-example`

The manuscript now proves substitutability through `β`, the admissible entry-height set `Q(x)`, the criterion (⋆) and the concatenation identity (⋆⋆). Lean proves the **same statement** by a different route (`DeltaStarFixedHSubstitutability`).

**Definitions compared.**

| manuscript | Lean | relation |
|---|---|---|
| `Δ*` | `DeltaStar.Language` | proved equal to the block star (`starDerives_iff_language`) and to the displayed grammar |
| `h⋆(w) = (fst, lst, ba)` | `starTyping` (`starSummary`: first symbol, last symbol, contains-`ba`) | same summary |

**Conclusion compared.** `FixedHSubstitutable starTyping Language` is the manuscript's `∼_{h⋆}`-substitutability (`def:hsubst`). Bridging the proof routes is not needed.

**Independent sanity check (not Lean).** A brute-force script confirmed:
- all seven `Q`-examples of the manuscript (`ab, aa, λ, bb, ba, bbaa, baaba`);
- (⋆) for every word of length ≤ 8;
- (⋆⋆) for all `s, t` of length ≤ 5.

No discrepancy was found.

## 6. Status

`prop:nonlinear-rs-example`: **F**. Every clause is now a CI-verified Lean theorem.
