{-# OPTIONS --safe #-}

-- Telomare 3 machine-checked specification — CI entry point.
--
-- Every spec module must be imported here so that
-- `agda --safe Everything.agda` (the flake check `telomare3-spec`)
-- gates the whole specification. Discipline: --safe everywhere, zero
-- postulates; imported metatheory is cited in comments, never axiomatized.
--
-- M1: the core category and its semantics, ported and consolidated from
-- design/telomare2.agda (frozen).  M3 adds T3.Surface.* and T3.Place;
-- M4 adds T3.Abstract.*; M5 attempts T3.Resource.Monoid + T3.Sem.Length.
module Everything where

import T3.Core.Ty
import T3.Core.Syntax
import T3.Sem.Value
import T3.Sem.Graded
import T3.Sem.Exec
import T3.Adequacy
import T3.Examples.Basics
import T3.Surface.Ty
import T3.Surface.Syntax
import T3.Surface.Sem
import T3.Place
import T3.Abstract
import T3.Examples.Budgets
import T3.Sem.Length
