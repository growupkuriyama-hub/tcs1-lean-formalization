import LeanCfgProject.TCS1.V135MainTheoremItemIV
import LeanCfgProject.TCS1.V135PolyBuildBridge

/-!
# TCS #1 v135: kernel axiom audit for the new paper-facing theorems

Each `#guard_msgs` block below makes the build **fail** unless the printed
dependency list is exactly Lean's three standard axioms.  In particular a
hidden `sorryAx` or any project-level axiom anywhere in the dependency cone
would change the message and break CI.
-/

namespace LeanCfgProject
namespace TCS1

/--
info: 'LeanCfgProject.TCS1.cor_liThickness_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cor_liThickness_exact

/--
info: 'LeanCfgProject.TCS1.cor_liThickness_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cor_liThickness_bound

/--
info: 'LeanCfgProject.TCS1.thm_main_item_iv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms thm_main_item_iv

/--
info: 'LeanCfgProject.TCS1.thm_main_item_iv_fixedWindow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms thm_main_item_iv_fixedWindow

/--
info: 'LeanCfgProject.TCS1.PolyBuild.thm_polyBuild' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PolyBuild.thm_polyBuild

end TCS1
end LeanCfgProject
