from rdkit import Chem

from typing import Iterable, List, Callable, Any, Tuple

import numpy as np
import time
import math

# How to use:
# Invoke the file using: python3 src/resources/RDKit/zincProfile.py
#
# while being in the top-level folder (idris2-chem)
#
# Adjust the queries at the bottom of the file.


# Settings --------------------------------------------------------------------
path = "resources/zinc.txt"

# See: https://stackoverflow.com/questions/287871/how-do-i-print-colored-text-to-the-terminal
class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


# Time measurement utility functions ------------------------------------------
def repeat(f: Callable[[None],Any],count: int) -> Any:
    i = 1; # Start at count 1 to skip the one which will be used to return
           # The return value
    while i < count:
        f()
        i = i + 1
    return f()

def measureTime(f: Callable[[None],Any], count: int) -> Tuple[float,Any]:
    start = time.time()
    res = repeat(f,count)
    end = time.time()
    return (end - start, res)

def prettyTime(tPassed: float) -> str:
    e10 = math.ceil(np.abs(np.log10(tPassed)))
    if e10 >= 0:
        return (str(tPassed) + " s")
    if e10 <= 3:
        return (str(tPassed*1000) + " ms")
    if e10 <= 6:
        return (str(tPassed*1000000) + " μs")
    return (str(tPassed*1000000000) + " ns")

def printStats(desc: str, count: int, tPassed):
    print('\n-',desc, '-')
    print('Executions:   ',count)
    print('Total time:   ',prettyTime(tPassed))
    print('Average time: ',prettyTime(tPassed/count))
    return


def measureAndReport(f: Callable[[None],Any], desc: str, count: int) -> Any:
    (t,res) = measureTime(f, count)
    printStats(desc, count,t)
    return res


# RDKit utility functions -----------------------------------------------------

# Matching result accumulators - RDKit
def countMatches(query: Chem.rdchem.Mol, molList: Iterable[Chem.rdchem.Mol]) -> int:
    n = 0
    for t in molList:
        if t is None:
            print(f"{bcolors.WARNING}[Warning] countMatches: NoneType found!{bcolors.ENDC}")
        else:
            if t.HasSubstructMatch(query): n = n + 1;
    return n

def showMatchingOutcome(query: str, molList: Iterable[Chem.rdchem.Mol]):
    return

# Data accessors - ZINC
def getZincSMILES(path: str) -> List[str]:
    with open(path,'r') as fh:
      smilesList = fh.readlines()
      fh.close()
    return smilesList

def getZincMolecules(path: str) -> Iterable[Chem.rdchem.Mol]:
    ls = getZincSMILES(path)
    return map(Chem.MolFromSmiles,ls)


# Profiling functionality -----------------------------------------------------

def profileIsomorphism(query: str, targets: Iterable[Chem.rdchem.Mol], count: int):
    qry = Chem.MolFromSmiles(query)
    print('Searching matches for query:',query)
    f        = lambda: countMatches(qry,targets)
    nMatches = measureAndReport(f,'ZINC matching only',count)
    print('Number of matches:',nMatches)


def profileMatchingSeparately(query: Iterable[str], count: int):
    print('----- Loading ZINC molecules -----')
    g        = lambda: list(getZincMolecules(path)) # A list dramatically increases matching speed after (iterable probably)
    trgs     = measureAndReport(g,'ZINC parsing',1)
    print(f"{bcolors.OKGREEN}\n[Info] Molecules loaded\n\n{bcolors.ENDC}")
    print('----- Isomorphism search -----\n')
    for q in query:
       profileIsomorphism(q,trgs,count)
       print('')
    return

# Execution -------------------------------------------------------------------
print('--------- RDKit profiling ---------')

# Measure time with parsing and substructure search
# Parsing takes a lot of time

# Measure time only for substructure search
profileMatchingSeparately(["CC(=O)C", "c1ccccc1O"],3)
