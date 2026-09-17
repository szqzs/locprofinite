import Aoki

/-!
Run `lake env lean AxiomAudit.lean` after `lake build`.
The main results must use only Lean's standard axioms `propext`,
`Classical.choice`, and `Quot.sound`, with no proof placeholders or
additional mathematical assumptions.
-/

#print axioms Aoki.aoki_question_2_14
#print axioms Aoki.aoki_question_2_14_minimality
#print axioms Aoki.aoki_example_cohomology_above
#print axioms Aoki.Cech.cupPower_degreeOneClass_top
#print axioms Aoki.Cech.aleph_cupPower_ne_zero
#print axioms Aoki.Cech.cupPower_next_eq_zero
#print axioms Aoki.Cech.cupCohomologyAddEquiv
#print axioms Aoki.Cech.yonedaPower_cupExtClass
#print axioms Aoki.Cech.cupIterate_comparison
#print axioms Aoki.Cech.aleph_topPowerClass_ne_zero
#print axioms Aoki.Cech.freeOpenProjectiveResolution
#print axioms Aoki.Cech.freeOpenModuleProjectiveResolution
#print axioms Aoki.freeOpen_iSup_projectiveDimensionLE
#print axioms Aoki.Geometry.mk_U
#print axioms Aoki.Geometry.weight_U
#print axioms Aoki.aleph_nondecomposition
#print axioms Aoki.almostConstant_iff_exists_continuous_extension
