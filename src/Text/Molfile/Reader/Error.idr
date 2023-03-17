module Text.Molfile.Reader.Error

import Derive.Prelude
import Text.ParseError

%default total

%language ElabReflection

public export
data MolFileError : Type where
  EEdge                 : MolFileError
  EHeader               : MolFileError
  EChiralFlag           : String -> MolFileError
  EVersion              : String -> MolFileError
  ESymbol               : String -> MolFileError
  EStereoParity         : String -> MolFileError
  EStereoCareBox        : String -> MolFileError
  EH0Designator         : String -> MolFileError
  EBondType             : String -> MolFileError
  EBondStereo           : String -> MolFileError
  EBondTopo             : String -> MolFileError

%runElab derive "MolFileError" [Show,Eq]

export
Interpolation MolFileError where
  interpolate v = "Invalid " ++ case v of
    EEdge                   => "bond"
    EHeader                 => ".mol-file header"
    EChiralFlag s           => "chiral flag: '\{s}'"
    EVersion s              => ".mol-file version: '\{s}'"
    ESymbol s               => "atom symbol: '\{s}'"
    EStereoParity s         => "stereo parity: '\{s}'"
    EStereoCareBox s        => "stereo care box: '\{s}'"
    EH0Designator s         => "H0 designator: '\{s}'"
    EBondType s             => "bond type: '\{s}'"
    EBondStereo s           => "bond stereo: '\{s}'"
    EBondTopo s             => "bond topology: '\{s}'"

public export
0 Error : Type
Error = ParseError Void MolFileError

export %inline
custom : MolFileError -> Either Error a
custom = Left . Custom

export
customPack : SnocList Char -> (String -> MolFileError) -> Either Error a
customPack sc f = custom (f . pack $ sc <>> [])
