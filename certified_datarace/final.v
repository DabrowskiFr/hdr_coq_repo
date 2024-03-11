Require Export points_to_semantic.
Require Export escape.
Require Export sem_equiv.
Require Export semantic_equiv.
Require Export points_to_race.


Module EquivProp := SemEquivProp StandardSemantic PointsToSemantic. 
Module CountingPointsToSemantic := CountingSemantic PointsToSemantic.C.
Module E := MakeEscape PointsToSemantic CountingPointsToSemantic.
Module Equiv := CountingSemanticEquiv PointsToSemantic CountingPointsToSemantic.
Module PointsToRace := MakePointsToRace PointsToSemantic.

Theorem OriginalPair_sound : forall p ppt1 ppt2,
  Sem.race p ppt1 ppt2 -> OriginalPair ppt1 ppt2.
Proof OriginalPair_sound.

Theorem ReachablePairs_sound : forall p PT,
  PointsToRace.PT.PointsToSpec p PT ->
  PointsToRace.PT.ValidReturns p ->
  forall ppt1 ppt2,
    Sem.race p ppt1 ppt2 -> PointsToRace.ReachablePairs p PT ppt1 ppt2.
Proof PointsToRace.ReachablePairs_sound.

Theorem AliasingPair_sound : forall p PT,
  PointsToRace.PT.PointsToSpec p PT ->
  PointsToRace.PT.ValidReturns p ->
  forall ppt1 ppt2,
    Sem.race p ppt1 ppt2 -> PointsToRace.AliasingPair p PT ppt1 ppt2.
Proof PointsToRace.AliasingPair_sound.

Theorem UnlockedPairs_sound : forall p PT ML M Frs Sigma,
  safe_loop p ->
  E.RR.ML.CPT.PTR.PT.PointsToSpec p PT ->
  E.RR.ML.P.MustLockSpec p (E.RR.ML.CPT.PTR.PT.ptL PT) 
    (E.RR.ML.CPT.PTR.PT.ptM PT) ML ->
  E.RR.DR.TS.T.typing p (E.RR.ML.CPT.PTR.PT.ptM PT) M Frs Sigma ->
  E.RR.ML.CPT.PTR.PT.ValidReturns p ->
  forall ppt1 ppt2,
    Sem.race p ppt1 ppt2 -> E.RR.UnlockedPairs p PT ML Sigma ppt1 ppt2.
Proof E.RR.UnlockedPairs_sound.

Theorem EscapingPairs_sound : forall p PT ML M Frs Sigma E,
  safe_loop p ->
  E.RR.ML.CPT.PTR.PT.PointsToSpec p PT ->
  E.RR.ML.P.MustLockSpec p (E.RR.ML.CPT.PTR.PT.ptL PT) 
    (E.RR.ML.CPT.PTR.PT.ptM PT) ML ->
  E.RR.DR.TS.T.typing p (E.RR.ML.CPT.PTR.PT.ptM PT) M Frs Sigma ->
  E.escape_typing p Frs E ->     
  E.RR.ML.CPT.PTR.PT.ValidReturns p ->
  forall ppt1 ppt2,
    Sem.race p ppt1 ppt2 -> E.EscapingPairs p PT ML Frs Sigma E ppt1 ppt2.
Proof E.EscapingPairs_sound.





