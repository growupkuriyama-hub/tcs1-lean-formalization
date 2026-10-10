import LeanCfgProject.TCS1.V144SSBNFFrontEnd

/-!
# TCS #1 v144: a run of the executable SSBNF normalizer

Grammar `S → a S b | ε` (`a = true`, `b = false`).  The normalizer writes the
reduced SSBNF grammar with nonterminals `S`, `W_a`, `W_b` and the suffix state
`[S b]`:

* terminal rules `W_a → a`, `W_b → b`, `[S b] → b` (the last one copied by unit
  elimination from the ε-elimination unit rule `[S b] → W_b`);
* binary rules `S → W_a [S b]`, `[S b] → S W_b`;
* start child `S`, ε flag set.

The `#guard`s evaluate the compiled normalizer and check these sizes and the
step counts reported by the same recursion.
-/

namespace LeanCfgProject
namespace TCS1
namespace SSBNFNorm
namespace Example

def nts : List (Fin 1) := [0]
def alph : List Bool := [true, false]
def prs : List (Fin 1 × List (MixedSymbol (Fin 1) Bool)) :=
  [(0, [Sum.inr true, Sum.inl 0, Sum.inr false]), (0, [])]

def run : Trace (FrontEndState (Fin 1) Bool) Bool :=
  normalizeTrace stateEqC (frontCodeC nts alph prs).1 (BinarizedState.old (Sum.inl 0))

#guard run.out.nonterminals.length = 4
#guard run.out.terminal.length = 3
#guard run.out.binary.length = 2
#guard run.out.start = some (BinarizedState.old (Sum.inl 0))
#guard run.out.epsilon = true
#guard (BinarizedState.suffix [Sum.inl 0, Sum.inr false], false) ∈ run.out.terminal
#guard run.steps + (frontCodeC nts alph prs).2 = 4313

end Example
end SSBNFNorm
end TCS1
end LeanCfgProject
