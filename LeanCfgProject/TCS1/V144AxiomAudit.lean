import LeanCfgProject.TCS1.V144SSBNFNormalize
import LeanCfgProject.TCS1.V144LinearSeparatorExists

/-!
# TCS #1 v144: kernel axiom audit for the new paper-facing theorems

Each `#guard_msgs` block makes the build fail unless the printed dependency
list is exactly Lean's three standard axioms (no `sorryAx`, no project axiom).
-/

namespace LeanCfgProject
namespace TCS1

/--
info: 'LeanCfgProject.TCS1.SSBNFNorm.prop_thickSSBNFNormal_executable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SSBNFNorm.prop_thickSSBNFNormal_executable

/--
info: 'LeanCfgProject.TCS1.SSBNFNorm.prop_thickSSBNFNormal_executable_degenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SSBNFNorm.prop_thickSSBNFNormal_executable_degenerate

/--
info: 'LeanCfgProject.TCS1.SSBNFNorm.normalizeSSBNF_steps_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SSBNFNorm.normalizeSSBNF_steps_le

/--
info: 'LeanCfgProject.TCS1.prop_linearSeparatorExample_existsH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prop_linearSeparatorExample_existsH

end TCS1
end LeanCfgProject
