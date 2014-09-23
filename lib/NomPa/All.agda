module NomPa.All where
import NomPa.Record
import NomPa.Derived
import NomPa.Derived.NaPa
import NomPa.Traverse
import NomPa.Implem
import NomPa.Examples.LC.DataTypes
import NomPa.Examples.LC.Contexts
import NomPa.Examples.LC.Equiv
-- import NomPa.Examples.LC.Monadic
-- import NomPa.Examples.LC.Monadic.Tests
import NomPa.Examples.LC.DbLevels
import NomPa.Examples.NaPa.LC
import NomPa.Examples.LC.Combined
import NomPa.Examples.LC
import NomPa.Examples.Records
-- import NomPa.Examples.Records.TypedVec
-- import NomPa.Examples.Records.Typed
import NomPa.Laws
import NomPa.Link
import NomPa.NomT
import NomPa.NomT.Maybe

-- Normalization By Evaluation
import NomPa.Examples.NBE
import NomPa.Examples.NBE.Can
import NomPa.Examples.NBE.Env
import NomPa.Examples.NBE.Neu
import NomPa.Examples.NBE.Tests

-- bare, raw, non-fancy…
import NomPa.Examples.BareDB
import NomPa.Examples.Raw
import NomPa.Examples.Raw.Parser
import NomPa.Examples.Raw.Printer
import NomPa.Examples.LC.WellScopedJudgment

-- Encodings: Emebedding of nominal types
import NomPa.Encodings.NominalTypes
import NomPa.Encodings.NominalTypes.Generic
import NomPa.Encodings.NominalTypes.Generic.Subst
import NomPa.Encodings.NominalTypes.Generic.Combined
import NomPa.Encodings.NominalTypes.MultiSorts
import NomPa.Encodings.NominalTypes.MultiSorts.Test
import NomPa.Encodings.AlphaCaml
import NomPa.Encodings.AlphaCaml.Test
import NomPa.Encodings.BindersUnbound
import NomPa.Encodings.BindersUnbound.Generic

-- Algorithms
import NomPa.Examples.LC.CC
import NomPa.Examples.LC.Monadic
import NomPa.Examples.LC.Monadic.Tests

-- hybrid
import NomPa.Examples.LN
import NomPa.Examples.LL
import NomPa.Examples.LocallyNamed

-- More examples
import NomPa.Examples.LC.Maybe
import NomPa.Examples.LC.SymanticsTy
import NomPa.Examples.LC.Tests
import NomPa.Examples.LocallyClosed
import NomPa.Examples.PTS
import NomPa.Examples.PTS.F
import NomPa.Examples.Reg

-- Tests
import NomPa.Examples.Tests

-- Logical relations
import NomPa.Record.LogicalRelation
import NomPa.Implem.LogicalRelation
import NomPa.Examples.LC.DataTypes.Logical

-- Universal types
import NomPa.Universal.RegularTree
import NomPa.Universal.Sexp

import NomPa.Derived.WorldInclusion
