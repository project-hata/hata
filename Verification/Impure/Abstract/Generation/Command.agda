
module Verification.Impure.Abstract.Generation.Command where

open import Verification.Conventions.Meta.Term
open import Verification.Impure.SpecialConventions
open import Verification.Impure.IO.Definition

data GenerationCommand : 𝒰₀ where
  generateFile : FilePath -> Text -> GenerationCommand
  editFile : FilePath -> Text -> Text -> Text -> GenerationCommand

postulate
  generate : GenerationCommand -> IO 𝟙-𝒰

--------------------------------------------------
-- BEGIN Generated 1

-- ...

-- END Generated 1
--------------------------------------------------


--------------------------------------------------
-- BEGIN Generated 2

-- ...

-- END Generated 2
--------------------------------------------------


