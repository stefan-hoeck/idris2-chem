module Text.Molfile.Reader.Error

import Derive.Prelude
import Text.Parse.Manual

%default total

%language ElabReflection

public export
data MolErr : Type where
  EEdge                 : MolErr
  EHeader               : MolErr
  EChiralFlag           : String -> MolErr
  EDot                  : Char -> MolErr
  EVersion              : String -> MolErr
  ESymbol               : String -> MolErr
  ERadical              : String -> MolErr
  EStereoParity         : String -> MolErr
  EStereoCareBox        : String -> MolErr
  EH0Designator         : String -> MolErr
  EBondType             : String -> MolErr
  EBondStereo           : String -> MolErr
  EBondTopo             : String -> MolErr
  EOutOfBounds          : Nat -> MolErr
  EInvalid              : String -> MolErr
  ECoordinate           : String -> MolErr
  EOI                   : MolErr

%runElab derive "MolErr" [Show,Eq]

export
packError : SnocList Char -> (String -> MolErr) -> Either MolErr a
packError sc f = Left . f . pack $ sc <>> []

export
Interpolation MolErr where
  interpolate v = "Invalid " ++ case v of
    EEdge                   => "bond"
    EHeader                 => ".mol-file header"
    EChiralFlag s           => "chiral flag: '\{s}'"
    EVersion s              => ".mol-file version: '\{s}'"
    ESymbol s               => "atom symbol: '\{s}'"
    ERadical s              => "radical: '\{s}'"
    EStereoParity s         => "stereo parity: '\{s}'"
    EStereoCareBox s        => "stereo care box: '\{s}'"
    EH0Designator s         => "H0 designator: '\{s}'"
    EBondType s             => "bond type: '\{s}'"
    EBondStereo s           => "bond stereo: '\{s}'"
    EBondTopo s             => "bond topology: '\{s}'"
    EOutOfBounds s          => "value: '\{show s}'"
    EInvalid s              => "string: '\{s}'"
    EDot c                  => "dot: \{show c}"
    ECoordinate s           => "coordinate: '\{s}'"
    EOI                     => "end of input"

public export
record MolParseErr where
  constructor MPE
  line  : Nat
  error : MolErr

%runElab derive "MolParseErr" [Eq,Show]

export
Interpolation MolParseErr where
  interpolate (MPE l e) = "Error in .mol file line \{show l}: \{e}"
