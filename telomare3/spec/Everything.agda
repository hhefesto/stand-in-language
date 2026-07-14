{-# OPTIONS --safe #-}

-- Telomare 3 machine-checked specification — CI entry point.
--
-- Every spec module must be imported here so that
-- `agda --safe Everything.agda` (the flake check `telomare3-spec`)
-- gates the whole specification. Discipline: --safe everywhere, zero
-- postulates; imported metatheory is cited in comments, never axiomatized.
--
-- M0: intentionally empty. M1 populates T3.Core.*, T3.Sem.*, T3.Adequacy,
-- T3.Examples.* (ported and consolidated from design/telomare2.agda).
module Everything where
