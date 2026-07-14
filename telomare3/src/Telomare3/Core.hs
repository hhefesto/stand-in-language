-- | Telomare 3 core.
--
-- M0 placeholder. From M2 this module mirrors the Agda specification in
-- @telomare3/spec/T3/Core/Syntax.agda@ constructor-for-constructor; until
-- then it only proves the package builds and is wired into the flake.
module Telomare3.Core
  ( telomare3Version
  ) where

-- | Version string reported by the @telomare3@ executable.
telomare3Version :: String
telomare3Version = "telomare3 0.1.0.0 (M0 scaffolding)"
