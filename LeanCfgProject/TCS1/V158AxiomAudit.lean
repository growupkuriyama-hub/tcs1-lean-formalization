import LeanCfgProject.TCS1.V158DeltaStarDCFLPackage
import LeanCfgProject.TCS1.V158CounterDyckDPDA

/-!
# TCS #1 v158: kernel axiom audit for the new paper-facing theorems

Each `#guard_msgs` block fails the build unless the dependency list is exactly
Lean's standard axioms.  `DPDA.step_deterministic` uses no axiom at all.
-/

namespace LeanCfgProject
namespace TCS1

/--
info: 'LeanCfgProject.TCS1.DPDA.step_deterministic' does not depend on any axioms
-/
#guard_msgs in
#print axioms DPDA.step_deterministic

/--
info: 'LeanCfgProject.TCS1.DeltaStar.deltaStar_isDCFL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms DeltaStar.deltaStar_isDCFL

/--
info: 'LeanCfgProject.TCS1.DeltaStar.nonlinear_rs_example_full_dcfl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms DeltaStar.nonlinear_rs_example_full_dcfl

/--
info: 'LeanCfgProject.TCS1.UncappedCounter.uncappedCounter_isDCFL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms UncappedCounter.uncappedCounter_isDCFL

/--
info: 'LeanCfgProject.TCS1.DyckOne.dyckOne_isDCFL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms DyckOne.dyckOne_isDCFL

end TCS1
end LeanCfgProject
