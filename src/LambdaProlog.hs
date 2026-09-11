-- | Public API for the λProlog kernel. Surface language, driver, and CLI are
-- re-exported from here as they land.
module LambdaProlog
  ( -- * Names
    Name (..)
  , Interner
  , emptyInterner
  , intern
  , internMany
  , lookupName
  , nameText
    -- * Spans and errors
  , SrcPos (..)
  , SrcSpan (..)
  , Located (..)
  , dummySpan
  , Error (..)
  , mkError
  , mkErrorAt
  , renderError
    -- * Kinds and types
  , Kind (..)
  , kindArity
  , Type (..)
  , Scheme (..)
  , tyArrs
  , tyArgs
  , tyArity
    -- * Terms
  , Level (..)
  , MetaId (..)
  , Lit (..)
  , Head (..)
  , Term (..)
  , var
  , con
  , meta
  , lit
  , intLit
  , stringLit
  , lam
  , lams
  , unLams
  , app
  , apps
  , applySpine
  , shift
  , instantiate
  , betaNf
  , etaExpand
    -- * Unification
  , UnifyError (..)
  , unifyPure
    -- * Search
  , Atom (..)
  , Goal (..)
  , Clause (..)
  , Program
  , emptyProgram
  , consultClauses
  , Solution (..)
  , query
  , queryN
    -- * Driver
  , Loaded (..)
  , ModuleQueryResult (..)
  , loadFile
  , loadFileQuiet
  , loadSource
  , runQueryText
    -- * Game driver
  , playGame
  , runGameTurn
  , initGameSession
    -- * Pretty-printing
  , PrintEnv (..)
  , mkPrintEnv
  , prettyKind
  , prettyType
  , prettyTerm
  , renderKind
  , renderType
  , renderTerm
  ) where

import LambdaProlog.Game
  ( initGameSession
  , playGame
  , runGameTurn
  )
import LambdaProlog.Error
  ( Error (..)
  , mkError
  , mkErrorAt
  , renderError
  )
import LambdaProlog.Kernel.Goal
  ( Atom (..)
  , Clause (..)
  , Goal (..)
  , Program
  , consultClauses
  , emptyProgram
  )
import LambdaProlog.Kernel.Kind (Kind (..), kindArity)
import LambdaProlog.Driver
  ( Loaded (..)
  , ModuleQueryResult (..)
  , loadFile
  , loadFileQuiet
  , loadSource
  , runQueryText
  )
import LambdaProlog.Kernel.Search (Solution (..), query, queryN)
import LambdaProlog.Kernel.Pretty
  ( PrintEnv (..)
  , mkPrintEnv
  , prettyKind
  , prettyTerm
  , prettyType
  , renderKind
  , renderTerm
  , renderType
  )
import LambdaProlog.Kernel.Subst (betaNf, etaExpand)
import LambdaProlog.Kernel.Unify (UnifyError (..), unifyPure)
import LambdaProlog.Kernel.Term
  ( Head (..)
  , Level (..)
  , Lit (..)
  , MetaId (..)
  , Term (..)
  , app
  , applySpine
  , apps
  , con
  , instantiate
  , intLit
  , lam
  , lams
  , lit
  , meta
  , shift
  , stringLit
  , unLams
  , var
  )
import LambdaProlog.Kernel.Type
  ( Scheme (..)
  , Type (..)
  , tyArgs
  , tyArity
  , tyArrs
  )
import LambdaProlog.Name
  ( Interner
  , Name (..)
  , emptyInterner
  , intern
  , internMany
  , lookupName
  , nameText
  )
import LambdaProlog.Span
  ( Located (..)
  , SrcPos (..)
  , SrcSpan (..)
  , dummySpan
  )

