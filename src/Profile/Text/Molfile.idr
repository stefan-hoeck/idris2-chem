module Profile.Text.Molfile

import Data.Either
import Data.List
import Data.Nat
import Data.String
import Data.Vect
import Text.Molfile
import Text.RW
import Profile.Profiler

-- One of the larger molecules in CyBy
mf : String
mf = #"""
     Molecule from ChemDoodle Web Components
       
     http://www.ichemlabs.com
      71 74  0  0  0  0            999 V2000
         4.0434    1.7194    0.0000 C   0  0  0  0  0  0
         4.3940   -1.1679    0.0000 C   0  0  0  0  0  0
        -4.2532   -4.3178    0.0000 C   0  0  0  0  0  0
        -3.2468    2.3278    0.0000 C   0  0  0  0  0  0
        -3.7091    3.0041    0.0000 C   0  0  0  0  0  0
        -2.4218    2.3278    0.0000 O   0  0  0  0  0  0
        -3.2242    3.6715    0.0000 O   0  0  0  0  0  0
        -2.4218    0.8989    0.0000 C   0  0  0  0  0  0
        -4.5144   -3.5351    0.0000 O   0  0  0  0  0  0
        -2.6120   -2.4651    0.0000 C   0  0  0  0  0  0
        -3.1590   -3.0827    0.0000 C   0  0  0  0  0  0
        -3.9674   -2.9176    0.0000 C   0  0  0  0  0  0
        -4.2286   -2.1350    0.0000 C   0  0  0  0  0  0
        -3.6815   -1.5175    0.0000 C   0  0  0  0  0  0
        -2.8732   -1.6825    0.0000 C   0  0  0  0  0  0
        -2.3261   -1.0650    0.0000 C   0  0  0  0  0  0
        -2.0093    1.6134    0.0000 C   0  0  0  0  0  0
        -2.0022    0.2921    0.0000 O   0  0  0  0  0  0
        -1.5178   -1.2300    0.0000 C   0  0  0  0  0  0
        -0.9707   -0.6124    0.0000 C   0  0  0  0  0  0
        -1.1843    0.1844    0.0000 C   0  0  0  0  0  0
        -0.7718    0.8989    0.0000 N   0  0  0  0  0  0
         0.1059   -0.7652    0.0000 N   0  0  0  0  0  0
         0.8204   -2.0028    0.0000 O   0  0  0  0  0  0
         3.7266   -1.6527    0.0000 O   0  0  0  0  0  0
         0.8204   -1.1777    0.0000 C   0  0  0  0  0  0
         2.8014   -0.5104    0.0000 C   0  0  0  0  0  0
         2.9729   -1.3173    0.0000 C   0  0  0  0  0  0
         2.2585   -1.7297    0.0000 C   0  0  0  0  0  0
         1.6454   -1.1777    0.0000 C   0  0  0  0  0  0
         0.7434    0.2904    0.0000 O   0  0  0  0  0  0
         1.9809   -0.4240    0.0000 N   0  0  0  0  0  0
         3.2184    1.7194    0.0000 O   0  0  0  0  0  0
         3.2184    0.2904    0.0000 C   0  0  0  0  0  0
         2.8059    1.0049    0.0000 C   0  0  0  0  0  0
         1.5684    0.2904    0.0000 C   0  0  0  0  0  0
         1.9809    1.0049    0.0000 C   0  0  0  0  0  0
         2.3653    3.3619    0.0000 N   0  0  0  0  0  0
         2.8059    2.4338    0.0000 O   0  0  0  0  0  0
         1.5684    1.7194    0.0000 N   0  0  0  0  0  0
         1.9809    2.4338    0.0000 C   0  0  0  0  0  0
         1.5684    3.1482    0.0000 C   0  0  0  0  0  0
         1.9809    3.8628    0.0000 C   0  0  0  0  0  0
         1.5684    4.5773    0.0000 C   0  0  0  0  0  0
         0.7434    4.5773    0.0000 C   0  0  0  0  0  0
        -1.1843    1.6134    0.0000 C   0  0  0  0  0  0
         0.0532    2.3278    0.0000 O   0  0  0  0  0  0
        -0.7718    2.3278    0.0000 C   0  0  0  0  0  0
        -1.1843    3.0423    0.0000 N   0  0  0  0  0  0
        -1.9912    2.8707    0.0000 C   0  0  0  0  0  0
        -2.4037    3.5853    0.0000 C   0  0  0  0  0  0
        -1.8517    4.1984    0.0000 C   0  0  0  0  0  0
        -0.3835    5.1003    0.0000 O   0  0  0  0  0  0
         0.3309    3.8628    0.0000 N   0  0  0  0  0  0
        -0.3835    4.2752    0.0000 C   0  0  0  0  0  0
        -1.0980    3.8628    0.0000 C   0  0  0  0  0  0
         4.8684    1.7194    0.0000 C   0  0  0  0  0  0
         3.6309    1.0049    0.0000 C   0  0  0  0  0  0
         3.6309    2.4338    0.0000 C   0  0  0  0  0  0
         3.6404   -0.8323    0.0000 C   0  0  0  0  0  0
         5.0615   -0.6829    0.0000 C   0  0  0  0  0  0
         4.4803   -1.9884    0.0000 C   0  0  0  0  0  0
        -3.9919   -5.1002    0.0000 C   0  0  0  0  0  0
        -5.0615   -4.1527    0.0000 C   0  0  0  0  0  0
        -3.7061   -3.7002    0.0000 C   0  0  0  0  0  0
        -4.0718    2.3278    0.0000 C   0  0  0  0  0  0
        -2.8343    3.0423    0.0000 C   0  0  0  0  0  0
        -2.8343    1.6134    0.0000 C   0  0  0  0  0  0
        -4.1940    2.3367    0.0000 C   0  0  0  0  0  0
        -4.0447    3.7578    0.0000 C   0  0  0  0  0  0
        -2.8886    2.9179    0.0000 C   0  0  0  0  0  0
      33  1  1  0  0  0  0
      25  2  1  0  0  0  0
       9  3  1  0  0  0  0
       6  4  1  0  0  0  0
       7  5  1  0  0  0  0
      11 10  1  0  0  0  0
      12  9  1  0  0  0  0
      12 11  2  0  0  0  0
      13 12  1  0  0  0  0
      14 13  2  0  0  0  0
      15 10  2  0  0  0  0
      15 14  1  0  0  0  0
      16 15  1  0  0  0  0
      17  6  1  1  0  0  0
      17  8  1  0  0  0  0
      19 16  1  0  0  0  0
      20 19  1  0  0  0  0
      21 18  2  0  0  0  0
      21 20  1  0  0  0  0
      22 21  1  0  0  0  0
      20 23  1  1  0  0  0
      26 23  1  0  0  0  0
      26 24  2  0  0  0  0
      28 25  1  6  0  0  0
      28 27  1  0  0  0  0
      29 28  1  0  0  0  0
      30 26  1  0  0  0  0
      30 29  1  0  0  0  0
      32 27  1  0  0  0  0
      30 32  1  1  0  0  0
      35 33  1  6  0  0  0
      35 34  1  0  0  0  0
      36 31  2  0  0  0  0
      36 32  1  0  0  0  0
      37 35  1  0  0  0  0
      37 36  1  0  0  0  0
      37 40  1  1  0  0  0
      41 39  2  0  0  0  0
      41 40  1  0  0  0  0
      42 38  1  1  0  0  0
      42 41  1  0  0  0  0
      43 42  1  0  0  0  0
      44 43  1  0  0  0  0
      45 44  1  0  0  0  0
      46 17  1  0  0  0  0
      46 22  1  1  0  0  0
      48 46  1  0  0  0  0
      48 47  2  0  0  0  0
      49 48  1  0  0  0  0
      50 49  1  0  0  0  0
      51  7  1  6  0  0  0
      51 50  1  0  0  0  0
      52 51  1  0  0  0  0
      54 45  1  0  0  0  0
      55 53  2  0  0  0  0
      55 54  1  0  0  0  0
      56 49  1  0  0  0  0
      56 52  1  0  0  0  0
      56 55  1  1  0  0  0
       1 57  1  0  0  0  0
       1 58  1  0  0  0  0
       1 59  1  0  0  0  0
       2 60  1  0  0  0  0
       2 61  1  0  0  0  0
       2 62  1  0  0  0  0
       3 63  1  0  0  0  0
       3 64  1  0  0  0  0
       3 65  1  0  0  0  0
       4 66  1  0  0  0  0
       4 67  1  0  0  0  0
       4 68  1  0  0  0  0
       5 69  1  0  0  0  0
       5 70  1  0  0  0  0
       5 71  1  0  0  0  0
     M  END
     """#

mfMedium : String
mfMedium =
#"""
  
  CDK
  
 29 32  0  0  0  0  0  0  0  0999 V2000
    0.0004    9.7502    0.0000 F   0  0  0  0  0  0  0  0  0  0  0  0
    0.0001    8.2502    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
   -1.4770    8.5109    0.0000 F   0  0  0  0  0  0  0  0  0  0  0  0
   -0.5131    6.8408    0.0000 F   0  0  0  0  0  0  0  0  0  0  0  0
    1.2990    7.5000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    2.5990    8.2500    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    3.8990    7.5000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    3.8990    6.0000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    2.5990    5.2500    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    2.5990    3.7500    0.0000 N   0  0  0  0  0  0  0  0  0  0  0  0
    1.3000    3.0000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    0.0010    3.7500    0.0000 O   0  0  0  0  0  0  0  0  0  0  0  0
    1.3000    1.5000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    2.6000    0.7500    0.0000 N   0  0  0  0  0  0  0  0  0  0  0  0
    2.6000   -0.7500    0.0000 N   0  0  0  0  0  0  0  0  0  0  0  0
    1.3000   -1.5000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    1.3000   -3.0000    0.0000 O   0  0  0  0  0  0  0  0  0  0  0  0
   -0.0000   -0.7500    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
   -1.3000   -1.5000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
   -2.6000   -0.7500    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
   -2.6000    0.7500    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
   -1.3000    1.5000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
   -0.0000    0.7500    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    1.2990    6.0000    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    5.1980    5.2498    0.0000 N   0  0  0  0  0  0  0  0  0  0  0  0
    6.5596    5.8613    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    7.5659    4.7489    0.0000 N   0  0  0  0  0  0  0  0  0  0  0  0
    6.8214    3.4552    0.0000 C   0  0  0  0  0  0  0  0  0  0  0  0
    5.3497    3.7554    0.0000 N   0  0  0  0  0  0  0  0  0  0  0  0
  1  2  1  0  0  0  0 
  2  3  1  0  0  0  0 
  2  4  1  0  0  0  0 
  2  5  1  0  0  0  0 
  5  6  1  0  0  0  0 
  6  7  2  0  0  0  0 
  7  8  1  0  0  0  0 
  8  9  2  0  0  0  0 
  9 10  1  0  0  0  0 
 10 11  1  0  0  0  0 
 11 12  2  0  0  0  0 
 11 13  1  0  0  0  0 
 13 14  2  0  0  0  0 
 14 15  1  0  0  0  0 
 15 16  1  0  0  0  0 
 16 17  2  0  0  0  0 
 16 18  1  0  0  0  0 
 18 19  1  0  0  0  0 
 19 20  2  0  0  0  0 
 20 21  1  0  0  0  0 
 21 22  2  0  0  0  0 
 22 23  1  0  0  0  0 
 13 23  1  0  0  0  0 
 18 23  2  0  0  0  0 
  9 24  1  0  0  0  0 
  5 24  2  0  0  0  0 
  8 25  1  0  0  0  0 
 25 26  1  0  0  0  0 
 26 27  2  0  0  0  0 
 27 28  1  0  0  0  0 
 28 29  2  0  0  0  0 
 25 29  1  0  0  0  0 
M  END
"""#

atomStr : String
atomStr = "   -2.8343    1.6134    0.0000 C   0  0  0  0  0  0"

bondStr : String
bondStr = " 56 55  1  1  0  0  0"

-- before profiling, this was at about 670 us per run on my NUC
testMol : () -> Bool
testMol () = isRight $ mol mf

testMolMedium : () -> Bool
testMolMedium () = isRight $ mol mfMedium

testAtom : () -> Bool
testAtom () = isRight $ atom atomStr

testAtomChunks : () -> Bool
testAtomChunks () = isRight $ trimmedChunks atomChunks atomStr

testBond : () -> Bool
testBond () = isRight $ bond bondStr

testReadFloat : () -> Bool
testReadFloat () = isRight $ the (Either String Coordinate) (readMsg "-2.8343")

testReadAtomSymbol : () -> Bool
testReadAtomSymbol () =
  isRight $ the (Either String AtomSymbol) (readMsg "C")

testReadMassDiff : () -> Bool
testReadMassDiff () =
  isRight $ the (Either String MassDiff) (readMsg "1")

export
profile : IO ()
profile = do
  profileAndReport $
    MkTask "read large MolFile" testMol 1000 ItIsSucc
  profileAndReport $
    MkTask "read medium MolFile" testMolMedium 20000 ItIsSucc
  profileAndReport $
    MkTask "read atom line" testAtom 100000 ItIsSucc
  profileAndReport $
    MkTask "read bond line" testBond 100000 ItIsSucc
  profileAndReport $
    MkTask "make atom chunks" testAtomChunks 100000 ItIsSucc
  profileAndReport $
    MkTask "read Float" testReadFloat 1000000 ItIsSucc
  profileAndReport $
    MkTask "read AtomSymbol" testReadAtomSymbol 1000000 ItIsSucc
  profileAndReport $
    MkTask "read MassDiff" testReadMassDiff 1000000 ItIsSucc
