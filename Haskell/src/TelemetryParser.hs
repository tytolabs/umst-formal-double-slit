{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026 Santhosh Shyamsundar, Santosh Prabhu Shenbagamoorthy — Studio TYTO

module TelemetryParser
  ( EmittedStepRecord(..)
  , StepRecord(..)
  , TraceRecord(..)
  , parseTrace
  ) where

import Data.Aeson
import GHC.Generics
import qualified Data.ByteString.Lazy as B

-- | Represents the metadata embedded in nested tracing emissions
data EmittedStepRecord = EmittedStepRecord
  { thermodynamicAdmissible :: Maybe Value
  , confidence :: Maybe Double
  , stepMI :: Maybe Double
  , stepCost :: Maybe Double
  } deriving (Show, Generic)

instance FromJSON EmittedStepRecord

-- | Core struct tracking step density evolution and physics aggregates
data StepRecord = StepRecord
  { density_matrix_real :: Maybe [[Double]]
  , density_matrix_imag :: Maybe [[Double]]
  , path_weights :: Maybe [Double]
  , visibility :: Maybe Double
  , distinguishability :: Maybe Double
  , entropy_bits :: Maybe Double
  , temperature :: Maybe Double
  , trajMI :: Maybe Double
  , effortCost :: Maybe Double
  , emitted :: Maybe EmittedStepRecord
  } deriving (Show, Generic)

instance FromJSON StepRecord

-- | Traces stream sequence of generic physical step records
data TraceRecord = TraceRecord
  { steps :: [StepRecord]
  } deriving (Show, Generic)

instance FromJSON TraceRecord

-- | Main ingress entrypoint to parse `sim/out/sample.json` to structured logic
parseTrace :: FilePath -> IO (Either String TraceRecord)
parseTrace fp = eitherDecode <$> B.readFile fp
