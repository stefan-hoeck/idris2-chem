module Text.Molfile.Reader

import Data.String
import Data.Vect
import public Text.Molfile.Types

%default total

||| Tries to split a `String` into a vector of
||| chunks of exactly the given lengths.
||| Fails if the length of the string does not exactly match
||| the length of concatenated chunks.
public export
chunks : Vect n Int -> String -> Maybe (Vect n String)
chunks ns s = go 0 ns
  where go : (pos : Int) -> Vect k Int -> Maybe (Vect k String)
        go pos [] = if pos == cast (length s) then Just [] else Nothing
        go pos (x :: xs) = (strSubstr pos x s ::) <$> go (pos + x) xs

public export
trimmedChunks : Vect n Int -> String -> Maybe (Vect n String)
trimmedChunks ns s = map trim <$> chunks ns s

||| Chunks of the counts line. See `counts` for a description
||| of the format and types of chunks.
public export
countChunks : Vect 12 Int
countChunks = [3,3,3,3,3,3,3,3,3,3,3,6]

||| General format:
|||   aaabbblllfffcccsssxxxrrrpppiiimmmvvvvvv
|||
|||   aaa    : number of atoms
|||   bbb    : number of bonds
|||   lll    : number of atom lines
|||   ccc    : chiral flag
|||   vvvvvv : version
|||
||| The other fields are obsolete or no longer supported
||| and are being ignored by the parser.
public export
counts : String -> Maybe Counts
counts s = do
  [a,b,l,_,c,_,_,_,_,_,_,v] <- trimmedChunks countChunks s
  [| MkCounts (read a) (read b) (read l) (read s) (read v) |]

||| Chunks of an atom line. See `atom` for a description
||| of the format and types of chunks.
public export
atomChunks : Vect 16 Int
atomChunks = [10,10,10,4,2,3,3,3,3,3,3,3,3,3,3,3]

||| General format:
|||   xxxxx.xxxxyyyyy.yyyyzzzzz.zzzz aaaddcccssshhhbbbvvvHHHrrriiimmmnnneee
|||
|||   x,y,z : coordinates
|||   aaa   : atom symbol
|||   dd    : mass difference (superseded by M ISO line)
|||   ccc   : charge (superseded by M RAD and M CHG lines)
|||   sss   : atom stereo parity
|||   hhh   : hydrogen count + 1
|||   bbb   : stereo care box
|||   vvv   : valence
|||   HHH   : H0 designator
|||
|||   r and i are not used and ignored
public export
atom : String -> Maybe Atom
atom s = do
  [x,y,z,a,d,c,s,h,b,v,h0,_,_,m,n,e] <- trimmedChunks atomChunks s
  [| MkAtom (read x) (read y) (read z) (read a) (readMassDiff d) (read c)
            (read s) (readHydrogenCount h) (read b) (read v) (read h0)
            (readAtomRef m) (read n) (read e) |]

||| Chunks of a bond line. See `atom` for a description
||| of the format and types of chunks.
public export
bondChunks : Vect 7 Int
bondChunks = [3,3,3,3,3,3,3]


--- --------------------------------------------------------------------------------
--- -- Molfile reader function
--- 
--- -- | Reads the whole file
--- --
--- -- FOR SOME REASON, THERE ARE 0 VALUES FOR HYDROGEN COUNTS?!?
--- --
--- --   TODO: NO TEST suite YET
--- -- >>> let molfile1 = "CC(C)=O\nJME 2017-11-16 Wed Jun 02 17:08:39 GMT+200 2021\n\n  4  3  0  0  0  0  0  0  0  0999 V2000\n    1.2124    0.7000    0.0000 C   0  0  0  1  0  0  0  0  0  0  0  0\n    2.4248    0.0000    0.0000 C   0  0  0  1  0  0  0  0  0  0  0  0\n    1.2124    2.1000    0.0000 O   0  0  0  1  0  0  0  0  0  0  0  0\n    0.0000    0.0000    0.0000 C   0  0  0  1  0  0  0  0  0  0  0  0\n  1  2  1  0  0  0  0\n  1  3  2  0  0  0  0\n  1  4  1  0  0  0  0\nM  END"
--- -- >>> let molfile2 = "CC(C)=O\nJME 2017-11-16 Wed Jun 02 17:08:39 GMT+200 2021\n\n  4  3  0  0  0  0  0  0  0  0999 V2000\n    1.2124    0.7000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0\n    2.4248    0.0000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0\n    1.2124    2.1000    0.0000 O   0  0  0  0  0  0  0  0  0  0  0  0\n    0.0000    0.0000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0\n  1  2  1  0  0  0  0\n  1  3  2  0  0  0  0\n  1  4  1  0  0  0  0\nM  END"
--- -- >>> readMolFile molfile1
--- -- Success (MolFileData {metaData = MolMetadata {moleculeName = Just (Refined "CC(C)=O"), molFileInfo = Just (Refined "JME 2017-11-16 Wed Jun 02 17:08:39 GMT+200 2021"), comment = Nothing}, countsData = MolFileCounts {nAtoms = Refined 4, nBonds = Refined 3, nAtomLists = Refined 0, obsolete1 = Refined 0, chiralFlag = NonChiral, obsolete2 = Refined 0, obsolete3 = Refined 0, obsolete4 = Refined 0, obsolete5 = Refined 0, obsolete6 = Refined 0, nProperties = Refined 999, molVersion = Just V2000}, atomData = [MolFileAtom {x = MolCoordinate (Refined 1) (Refined 2124), y = MolCoordinate (Refined 0) (Refined 7000), z = MolCoordinate (Refined 0) (Refined 0), symbol = Element C, massDifference = Refined 0, charge = Charge (Refined 0), stereoParity = NoStereo, hydrogenCount = Refined 0, stereoCareBox = IgnoreStereo, valence = NoMarking, h0designator = H0NotSpecified, atomUnused1 = "0", atomUnused2 = "0", atomAtomMapping = Refined 0, invRetentionFlag = InvNotApplied, exactChangeFlag = ChangeNotApplied},MolFileAtom {x = MolCoordinate (Refined 2) (Refined 4248), y = MolCoordinate (Refined 0) (Refined 0), z = MolCoordinate (Refined 0) (Refined 0), symbol = Element C, massDifference = Refined 0, charge = Charge (Refined 0), stereoParity = NoStereo, hydrogenCount = Refined 0, stereoCareBox = IgnoreStereo, valence = NoMarking, h0designator = H0NotSpecified, atomUnused1 = "0", atomUnused2 = "0", atomAtomMapping = Refined 0, invRetentionFlag = InvNotApplied, exactChangeFlag = ChangeNotApplied},MolFileAtom {x = MolCoordinate (Refined 1) (Refined 2124), y = MolCoordinate (Refined 2) (Refined 1000), z = MolCoordinate (Refined 0) (Refined 0), symbol = Element O, massDifference = Refined 0, charge = Charge (Refined 0), stereoParity = NoStereo, hydrogenCount = Refined 0, stereoCareBox = IgnoreStereo, valence = NoMarking, h0designator = H0NotSpecified, atomUnused1 = "0", atomUnused2 = "0", atomAtomMapping = Refined 0, invRetentionFlag = InvNotApplied, exactChangeFlag = ChangeNotApplied},MolFileAtom {x = MolCoordinate (Refined 0) (Refined 0), y = MolCoordinate (Refined 0) (Refined 0), z = MolCoordinate (Refined 0) (Refined 0), symbol = Element C, massDifference = Refined 0, charge = Charge (Refined 0), stereoParity = NoStereo, hydrogenCount = Refined 0, stereoCareBox = IgnoreStereo, valence = NoMarking, h0designator = H0NotSpecified, atomUnused1 = "0", atomUnused2 = "0", atomAtomMapping = Refined 0, invRetentionFlag = InvNotApplied, exactChangeFlag = ChangeNotApplied}], bondData = [MolFileBond {atomA = Refined 1, atomB = Refined 2, bondType = SingleBond, bondStereo = NoBondStereo, bondUnused = "0", bondTopology = AnyTopology, rCenterStatus = Unmarked},MolFileBond {atomA = Refined 1, atomB = Refined 3, bondType = DoubleBond, bondStereo = NoBondStereo, bondUnused = "0", bondTopology = AnyTopology, rCenterStatus = Unmarked},MolFileBond {atomA = Refined 1, atomB = Refined 4, bondType = SingleBond, bondStereo = NoBondStereo, bondUnused = "0", bondTopology = AnyTopology, rCenterStatus = Unmarked}], propertyData = []})
--- readMolFile :: Text -> Validation [Text] MolFileData
--- readMolFile t =
---   let (header, r)  = first pMolHeader $ splitAt 3 $ lines t
---       (eCount, r1 ) = first (isSingleton "counts line") $ splitAt 1 r
---   in fromEither do
---       -- Get the counts
---       counts <- eCount  >>= toEither . pCountsLine
---       -- Extract atom & bond lines
---       (atomLines, r2) <- getNLines (unrefine $ nAtoms counts)  r1
---       (bondLines, r3) <- getNLines (unrefine $ nBonds counts) r2
---       -- Get the property lines
---       propertyLines <- getPropertyLines counts r3
---       toEither $ MolFileData <$> header <*> pure counts
---                            <*> traverse pMolAtomLine atomLines
---                            <*> traverse pMolBondLine bondLines
---                            <*> readPropertyBlock propertyLines
--- 
--- -- | Get an exact number of lines
--- getNLines :: Int -> [Text] -> Either [Text] ([Text],[Text])
--- getNLines count t =
---     bitraverse (hasLength "Invalid atom line number in: " count) pure
---     $ splitAt count t
--- 
--- -- | Collects the lines of a property block
--- --   If a version stamp is present, then the number of property lines
--- --   in the counts line is ignored and the lines until "M END" are collected.
--- --   If no version stamp is present, then 'mmm' lines are collected for reading.
--- --
--- -- Example
--- --
--- -- >>> let mc1 = MolFileCounts $$(refineTH 0) $$(refineTH 0) $$(refineTH 0) $$(refineTH 0) NonChiral $$(refineTH 0) $$(refineTH 0) $$(refineTH 0) $$(refineTH 0) $$(refineTH 0) $$(refineTH 4) Nothing
--- -- >>> let mc2 = MolFileCounts $$(refineTH 0) $$(refineTH 0) $$(refineTH 0) $$(refineTH 0) NonChiral $$(refineTH 0) $$(refineTH 0) $$(refineTH 0) $$(refineTH 0) $$(refineTH 0) $$(refineTH 4) (Just V2000)
--- -- >>> getPropertyLines mc1 ["a","b","M  END","c"]
--- -- Right ["a","b","M  END","c"]
--- -- >>> getPropertyLines mc2 ["a","b","M  END","c"]
--- -- Right ["a","b"]
--- -- >>> getPropertyLines mc2 ["a","b","M","c"]
--- -- Left ["No 'M  END' detected in property block"]
--- -- >>> getPropertyLines mc1 ["a","b"]
--- -- Left ["Invalid number of property lines in: a\nb\n"]
--- getPropertyLines :: MolCounts -> [Text] -> Either [Text] [Text]
--- getPropertyLines counts l =
---    let nProps = unrefine $ nProperties counts
---    in maybe
---    (hasLength "Invalid number of property lines in: " nProps $ take nProps l) -- No molversion -> take n
---    (\_ -> fmap collectTillEnd (hasEnd l))    -- Molversion -> take till "M  END"
---    (molVersion counts)
---   where
---     collectTillEnd ls = takeWhile (not . DT.isPrefixOf "M  END") ls
---     hasEnd ls         = if any (DT.isPrefixOf "M  END") ls
---                         then pure ls
---                         else Left ["No 'M  END' detected in property block"]
--- 
--- -- | Determine whether the length matches
--- hasLength :: Text -> Int -> [Text] -> Either [Text] [Text]
--- hasLength eT n ls = if length ls == n
---                     then pure ls
---                     else Left [eT <> unlines ls]
--- 
--- -- Line readers ---------------------------------------------------------------

--- 
--- 
--- -- | Reads a bind line
--- --
--- -- Example
--- --
--- -- >>> pMolBondLine " 11  2  8  1  6  2 13"
--- -- Success (MolFileBond {atomA = Refined 11, atomB = Refined 2, bondType = AnyBond, bondStereo = UpBond, bondUnused = "6", bondTopology = Chain, rCenterStatus = CenterBMBAandOC})
--- -- >>> pMolBondLine "  1  A  1 -3  0  4  0"
--- -- Failure ["Invalid Atom Number: A","Invalid Bond Stereoinformation: -3","Invalid Bond Topology: 4"]
--- -- >>> pMolBondLine " 11  2  8  1  6  2 13  d"
--- -- Failure ["Invalid line length (24) (specified 21) in ' 11  2  8  1  6  2 13  d'"]
--- pMolBondLine :: Text -> Validation [Text] MolBond
--- pMolBondLine t =
---   case splitBondLine t of
---      Success [a,b,bt,bs,u,topo,rc] -> MolFileBond
---                      <$> readAtomNr         a
---                      <*> readAtomNr         b
---                      <*> readBondType       bt
---                      <*> readBondStereo     bs
---                      <*> readUnused         u
---                      <*> readBondTopology   topo
---                      <*> readReactionCenter rc
---      Failure x -> Failure x
---      _ -> Failure $ pLineErrorMessage "splitBondLine"
--- 
--- --------------------------------------------------------------------------------
--- -- ReadProperties
--- 
--- -- | Read a whole property block
--- readPropertyBlock :: [Text] -> Validation [Text] [MolProperties]
--- readPropertyBlock = fmap join . traverse convertProperty . tokenizePropertyLines
--- 
--- 
--- -- Property tokenizer  .   .   .   .   .   .   .   .   .   .   .   .   .   .   .
--- 
--- -- | Converts the list of property lines into property entry tokens
--- tokenizePropertyLines :: [Text] -> [PropertyEntry]
--- tokenizePropertyLines []     = []
--- tokenizePropertyLines (x:xs) =
---    let tag                   = propertyEntryTag x
---        mayTagLines           = exactSplitAt (nTagLines tag) (x:xs)
---        -- (propertyEntry, rest) = convertProperty tag mayTagLines
---    in  (\(p,r) -> p : tokenizePropertyLines r) (convertProperty' tag mayTagLines)
---   where
---     convertProperty' :: PropertyTagFirst -> Maybe ([Text],[Text]) -> (PropertyEntry,[Text])
---     convertProperty' _                Nothing     = (UnknownProperty x, xs)
---     convertProperty' UnrecognizedTag  _           = (UnknownProperty x, xs)
---     convertProperty' (OneLineTag t)   _           = (OneLine t x, xs)
---     convertProperty' (SkipNTag n)    (Just (l,r)) = (IgnoreLines n l,r)
---     convertProperty' (TwoLinesTag t) (Just (l,r)) = (TwoLine t l, r)
--- 
--- -- | Determine the number of lines to read
--- --   The number of lines in the "S SKPnnn" line is variable
--- --   and is read using 'getSkipN'
--- --
--- -- >>> propertyEntryTag "S  SKP  3"
--- -- SkipNTag (Refined 3)
--- propertyEntryTag :: Text -> PropertyTagFirst
--- propertyEntryTag l = case DT.take 1 l of
---     "S" -> getSkipLineTag l
---     "M" -> getOneLineTag l
---     "A" -> TwoLinesTag AA
---     "V" -> TwoLinesTag VA
---     "G" -> TwoLinesTag AG
---     _   -> UnrecognizedTag
--- 
--- 
--- -- | Helper function for propertyEntryTag
--- --   Determine whether the skip n lines tag has a valid number.
--- --   If not, line is unrecognizable
--- getSkipLineTag :: Text -> PropertyTagFirst
--- getSkipLineTag t = case DT.breakOnEnd "S  SKP" t of
---               ("",_) -> UnrecognizedTag
---               (_,t')  -> maybe UnrecognizedTag SkipNTag $
---                           refineMaybe (textToIntPositive $ DT.strip t')
--- -- | Helper function for propertyEntryTag to read the sub
--- --   types of the M line properties.
--- getOneLineTag :: Text -> PropertyTagFirst
--- getOneLineTag t = case DT.take 6 t of
---   "M  CHG" -> OneLineTag CHG
---   "M  RAD" -> OneLineTag RAD
---   "M  ISO" -> OneLineTag ISO
---   "M  RBC" -> OneLineTag RBC
---   "M  SUB" -> OneLineTag SUB
---   "M  UNS" -> OneLineTag UNS
---   "M  LIN" -> OneLineTag LIN
---   "M  ALS" -> OneLineTag ALS
---   _        -> UnrecognizedTag
--- 
--- 
--- -- | Returns the number of lines to read from a tag
--- nTagLines :: PropertyTagFirst -> Int
--- nTagLines (SkipNTag n)     = unrefine n
--- nTagLines (OneLineTag _)   = 1
--- nTagLines (TwoLinesTag _)  = 2
--- nTagLines  UnrecognizedTag = 1
--- 
--- 
--- -- Read Tokens .   .   .   .   .   .   .   .   .   .   .   .   .   .   .   .   .
--- -- | Reads and atom alias given the whole
--- --   property line as input (the line identifier
--- --   must not be removed)
--- readAtomAlias :: [Text] -> Validation [Text] [MolProperties]
--- readAtomAlias (l1:l2:[]) =
---   let getAtomNr = readAtomReference . DT.strip . DT.drop 3 . DT.take 6
---   in  fmap pure $ AtomAlias <$> (getAtomNr l1)
---                             <*> (readAlias l2)
--- readAtomAlias r = Failure ["Atomalias invalid: " <> unlines r]
--- 
--- -- | Reads an atom value given the whole
--- --   property line as input (the line identifier
--- --   must not be removed)
--- readAtomValue :: [Text] -> Validation [Text] [MolProperties]
--- readAtomValue (l1:l2:[]) =
---   let getAtomNr = readAtomReference . DT.strip . DT.drop 3 . DT.take 6
---   in  fmap pure $ AtomValue <$> (getAtomNr l1)
---                             <*> (readValueText l2)
--- readAtomValue r = Failure ["Atomvalue invalid: " <> unlines r]
--- 
--- -- | Reads the group abbreviation given the whole
--- --   property line as input (the line identifier
--- --   must not be removed)
--- readGroupAbbreviation :: [Text] -> Validation [Text] [MolProperties]
--- readGroupAbbreviation (l1:l2:[]) =
---   let getAtomNr1 = readAtomReference . DT.strip . DT.drop 3 . DT.take 6
---       getAtomNr2 = readAtomReference . DT.strip . DT.drop 6 . DT.take 9
---   in  fmap pure $ GroupAbbrevation <$> (getAtomNr1 l1)
---                        <*> (getAtomNr2 l1)
---                        <*> (readAlias l2)
--- readGroupAbbreviation r = Failure ["Goup abbreviation invalid: " <> unlines r]
--- 
--- 
--- -- | Reads the entries in a line with max nn8 entries
--- --   this function does not evaluate the kind of line it just reads the
--- --   values encoded in the line
--- --
--- -- Example
--- -- >>> readLineNN8 readChargeProperty "M  CHG  2   1   1   4  -1"
--- -- Success [(Refined 1,Refined 1),(Refined 4,Refined (-1))]
--- readLineNN8 :: (Text -> Validation [Text] b)
---             -> Text
---             -> Validation [Text] [(AtomReference, b)]
--- readLineNN8 f t = fromEither $ groupLine readNN8 8 t >>=
---                    (toEither . traverse (readLineValuesNN8 f))
--- 
--- -- | Reads a Link atom line
--- --
--- -- Example
--- --
--- -- >>> readLineLIN "M  LIN  1   1   3   0   1"
--- -- Success [LinkAtom (Refined 1) (Refined 3) (Refined 0) (Refined 1)]
--- readLineLIN :: Text -> Validation [Text] [MolProperties]
--- readLineLIN t = fromEither $ groupLine readLIN 16 t >>=
---                  (toEither . traverse readLineValuesLIN)
--- 
--- -- | Groups n entries of a property line
--- --   If at least one entry can't be read, then the whole line is flagged as invalid
--- --   The line is passed as a whole (e.g. with the "M  RADnn8  ...")
--- --
--- -- Example
--- --
--- -- >>> groupLine readNN8 8 "M  CHG  1   8   3"
--- -- Right ["   8   3"]
--- -- >>> groupLine readLIN 16 "M  LIN  2   1   3   0   1   6   4   2   5"
--- -- Right ["   1   3   0   1","   6   4   2   5"]
--- groupLine :: (Num b, Enum b) =>
---              (Text -> Validation [Text] (Refined p b))
---              -> Int
---              -> Text -> Either [Text] [Text]
--- groupLine f n t =
---   let (tN, tR) = DT.splitAt 3 $ DT.drop 6 t
---       valN     = f tN
---       nEntryN  = fmap (\x -> [1..(unrefine x)]) valN -- list length of n entries
---       nEntryL  = toEither $ fmap (n <$) nEntryN      -- 8 = characters per entry
---   in  nEntryL >>= (\x -> toEither $ splitText x tR)
--- 
--- -- Repetitive code sections
--- -- | Refined line entry number to validate them
--- readNN8 :: Text -> Validation [Text] NN8
--- readNN8 t = prependErrorMessage ("Invalid nuber of line entries nn8): " <> t)
---            $ readAndRefine textToIntPositive $ DT.strip t
--- 
--- -- | Refined line entry number to validate them
--- readLIN :: Text -> Validation [Text] LIN
--- readLIN t = prependErrorMessage ("Invalid nuber of line entries LIN): " <> t)
---            $ readAndRefine textToIntPositive $ DT.strip t
--- 
--- -- | Refined line entry number to validate them
--- readN16 :: Text -> Validation [Text] N16
--- readN16 t = prependErrorMessage ("Invalid nuber of line entries LIN): " <> t)
---           $ readAndRefine textToIntPositive $ DT.strip t
--- 
--- -- | Reads the ALS line
--- -- TODO: Clean this mess up!
--- --
--- -- >>> readALSLine "M  ALS   1  2 F   He  Li"
--- -- Success [AtomList (Refined 1) (AtomSymbolList NormalList [Element He,Element Li])]
--- readALSLine :: Text -> Validation [Text] [MolProperties]
--- readALSLine t =
---   let (tA, tR)   = DT.splitAt 3 $ DT.drop 7 t
---       (tN, tR')  = DT.splitAt 3 tR
---       (tE, tR'') = DT.splitAt 3 tR'
---       nEntryV    = fmap (\x -> [1..(unrefine x)]) (readN16 tN)
---       nEntryL    = toEither $ fmap (4 <$) nEntryV
---       atomValuesT= nEntryL >>= (\x -> toEither $ splitAndTrimText x tR'')
---       atomValues = fromEither $ atomValuesT >>= (toEither . traverse readAtomSymbol)
---       vAtomSybols= AtomSymbolList <$> readAtomListType (DT.strip tE) <*> atomValues
---   in fmap pure $ AtomList <$> readAtomReference tA <*> vAtomSybols
--- 
--- 
--- -- | Reads an atom reference and a refined value from the following pattern:
--- --   ' aaa vvv'
--- --
--- -- >>> readLineValuesNN8 readChargeProperty "   1   3"
--- -- Success (Refined 1,Refined 3)
--- readLineValuesNN8 :: (Text -> Validation [Text] b)
---                     -> Text
---                     -> Validation [Text] (AtomReference, b)
--- readLineValuesNN8 f' t =
---   prependErrorMessage ("Invalid pattern in one line entry (' aaa vvv'): " <> t)
---   $ bitraverse (readAndRefine textToIntPositive . DT.strip) (f' . DT.strip)
---   $ DT.splitAt 4 t
--- 
--- 
--- -- | Reads Link atom values of the structure ' aaa vvv bbb ccc'
--- --
--- -- >>> readLineValuesLIN "   3   4   1   2"
--- -- Success (LinkAtom (Refined 3) (Refined 4) (Refined 1) (Refined 2))
--- readLineValuesLIN :: Text
---                   -> Validation [Text] (MolProperties)
--- readLineValuesLIN t =
---   let (t1,t2) = DT.splitAt 8 t
---       (tA,tV) = DT.splitAt 4 t1
---       (tB,tC) = DT.splitAt 4 t2
---   in prependErrorMessage ("Invalid pattern in LIN entry (' aaa vvv bbb ccc'): " <> t)
---   $ LinkAtom <$> readAtomReference tA <*> readLinkAtomRepetition tV
---              <*> readLinkAtomReference tB <*> readLinkAtomReference tC
--- 
--- -- | The validation is not traversed as invalid entries are simply ignored
--- convertProperty :: PropertyEntry -> Validation [Text] [MolProperties]
--- convertProperty (UnknownProperty t) = Failure [t]
--- convertProperty (IgnoreLines n ts)  = Success [SkipNextN n ts]
--- convertProperty (OneLine CHG t) = mapEntryToProperty PCharge readChargeProperty t
--- convertProperty (OneLine ISO t) = mapEntryToProperty PIsotope readIsotopeProperty t
--- convertProperty (OneLine RAD t) = mapEntryToProperty PRadical readRadicalProperty t
--- convertProperty (OneLine RBC t) = mapEntryToProperty RingBondCount readRingBondCountProperty t
--- convertProperty (OneLine SUB t) = mapEntryToProperty SubstitutionCount readSubstitutionCountProperty t
--- convertProperty (OneLine UNS t) = mapEntryToProperty UnsaturatedCount readUnsaturationProperty t
--- convertProperty (OneLine LIN t) = readLineLIN t
--- convertProperty (OneLine ALS t) = readALSLine t
--- convertProperty (TwoLine AA ts) = readAtomAlias ts
--- convertProperty (TwoLine VA ts) = readAtomValue ts
--- convertProperty (TwoLine AG ts) = readGroupAbbreviation ts
--- 
--- -- | Used to lift the reader function for a 1 line property
--- --   into the structure
--- --
--- -- >>> mapEntryToProperty PCharge readChargeProperty "M  CHG  2   1   1   4  -1"
--- -- Success [PCharge (Refined 1) (Refined 1),PCharge (Refined 4) (Refined (-1))]
--- mapEntryToProperty :: (AtomReference -> t -> b)
---                    -> (Text -> Validation [Text] t)
---                    -> Text
---                    -> Validation [Text] [b]
--- mapEntryToProperty fP fb = fmap (fmap \(a,v) -> fP a v)
---                          . readLineNN8 fb
--- 
--- 
--- -- Readers for individual Molproperty subtypes ---------------------------------
--- -- | Read a reference nnn of an atom
--- readAtomReference :: Text -> Validation [Text] AtomReference
--- readAtomReference = readAndRefine textToInt . DT.strip
--- 
--- -- | Reads an alias of an atom reference or a group abbreviation
--- readAlias :: Text -> Validation [Text] Alias
--- readAlias = pure
--- 
--- -- | Reads a text corresponding to a value.
--- --   It is not interpreted or checked in any way.
--- readValueText :: Text -> Validation [Text] ValueText
--- readValueText = pure
--- 
--- -- | Reads a charge encoded from a property line
--- readChargeProperty :: Text -> Validation [Text] ChargeProperty
--- readChargeProperty = readAndRefine textToInt . DT.strip
--- 
--- -- | Reads a radical encoded from a property line
--- readRadicalProperty :: Text -> Validation [Text] RadicalProperty
--- readRadicalProperty = readBounded . DT.strip
--- 
--- -- | Reads an isotope property
--- readIsotopeProperty :: Text -> Validation [Text] IsotopeProperty
--- readIsotopeProperty = maybe (pure DefaultIsotope)
---                       (\x -> Isotope <$> (readAndRefine textToInt x))
---                       . hasContent . DT.strip
--- 
--- -- | Reads a ring bond count
--- readRingBondCountProperty :: Text -> Validation [Text] RingBondCountProperty
--- readRingBondCountProperty = matchRingBondCount . DT.strip
--- 
--- -- | Matches a RingBondCount to the corresoinding representation
--- --
--- -- Example:
--- --
--- -- >>> matchRingBondCount "5"
--- -- Success R4
--- -- >>> matchRingBondCount "A4"
--- -- Failure ["Invalid ring bond count: A4"]
--- matchRingBondCount :: Text -> Validation [Text] RingBondCountProperty
--- matchRingBondCount "0"  = Success RBOff
--- matchRingBondCount "-1" = Success NoRingBonds
--- matchRingBondCount "-2" = Success AsDrawnRB
--- matchRingBondCount "2"  = Success R2
--- matchRingBondCount "3"  = Success R4
--- matchRingBondCount t    = maybe (Failure ["Invalid ring bond count: " <> t])
---                           (\x -> if x > 3 then Success R4 else
---                           (Failure ["Invalid ring bond count: " <> t]) )
---                           $ textToInt t
--- 
--- -- | Reads a substitution count
--- readSubstitutionCountProperty :: Text
---                               -> Validation [Text] SubstitutionCountProperty
--- readSubstitutionCountProperty = matchSubstitutionCount . DT.strip
--- 
--- -- | Substitution count interpretation
--- matchSubstitutionCount :: Text -> Validation [Text] SubstitutionCountProperty
--- matchSubstitutionCount "0"  = Success SUBOff
--- matchSubstitutionCount "-1" = Success NoSubstitution
--- matchSubstitutionCount "-2" = Success AsDrawnS
--- matchSubstitutionCount "1"  = Success S1
--- matchSubstitutionCount "2"  = Success S2
--- matchSubstitutionCount "3"  = Success S3
--- matchSubstitutionCount "4"  = Success S4
--- matchSubstitutionCount "5"  = Success S5
--- matchSubstitutionCount t    = maybe (Failure ["Invalid ring bond count: " <> t])
---                               (\x -> if x > 3 then Success S6 else
---                               (Failure ["Invalid substitution count: " <> t]) )
---                               $ textToInt t
--- 
--- -- | Reads the unsaturation property
--- readUnsaturationProperty :: Text -> Validation [Text] UnsaturationProperty
--- readUnsaturationProperty t =
---    case DT.strip t of
---     "0" -> pure UNSOff
---     "1" -> pure UNSOn
---     _   -> Failure ["Invalid unsaturation property: " <> t]
--- 
--- -- | Reads the reference of substituents bbb & ccc
--- --  Zero refers to link point on atoms with attachement information
--- readLinkAtomReference :: Text -> Validation [Text] LinkAtomReference
--- readLinkAtomReference = readAndRefine textToInt . DT.strip
--- 
--- -- | Reads the repetition in a link atom line
--- readLinkAtomRepetition :: Text -> Validation [Text] LinkAtomRepetition
--- readLinkAtomRepetition = readAndRefine textToInt . DT.strip
--- 
--- -- | Reads the number of entries present in an atom line
--- readLinkAtomListEntries :: Text -> Validation [Text] AtomListEntries
--- readLinkAtomListEntries = readAndRefine textToInt . DT.strip
--- 
--- -- | Reads the type in which the atom symbol list is handled
--- readAtomListType :: Text -> Validation [Text] AtomListType
--- readAtomListType "T" = Success NotList    -- Exclude the listed Atom symbols
--- readAtomListType "F" = Success NormalList -- Include the listed Atom symbols
--- readAtomListType t   = Failure ["Invalid atom list type: " <> t]
--- 
--- -- | Reads n entries of an atom list where the line property specification
--- --   was removed (M ALS ...)
--- readNAtomSymbols :: AtomListEntries
---                 -> Text
---                 -> Validation [Text] [MolAtomSymbol]
--- readNAtomSymbols n t = fold $ fmap (traverse readAtomSymbol) $ makeNChunks (unrefine n) t
--- 
--- -- | Helper function for readNAtomSymbols to tokenize the line input
--- makeNChunks :: Int -> Text -> Validation [Text] [Text]
--- makeNChunks n t =
---   let chuncks = DT.chunksOf 4 t
---       failure = Failure ["Invalid number of entries (" <> show n <>
---                          ") in symbol entry list: "    <> t]
---   in if Protolude.length chuncks /= n then failure else pure chuncks
--- 
--- -- | Reads an atom symbol list with a specified number of
--- readAtomSymbolList :: Text -> Validation [Text] AtomSymbolList
--- readAtomSymbolList t =
---   -- let (atomNr, t')     = DT.splitAt 3 t
---   let (nEntries, t'')  = DT.splitAt 3 t
---       (eV, symbollist) = DT.splitAt 3 t''
---       atomListType     = readAtomListType $ DT.strip eV
---       linkEntries      = readLinkAtomListEntries $ DT.strip nEntries
---   in AtomSymbolList <$> atomListType <*>
---      (fold (readNAtomSymbols <$> linkEntries <*> pure symbollist))
