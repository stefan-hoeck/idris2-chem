"""
Requires:      Installed RDKit
Ubuntu:        > sudo apt-get install python-rdkit librdkit1 rdkit-data
Installation:  https://www.rdkit.org/docs/Install.html

----

How to use:
Invoke the file using: python3 src/Profile/RDKit/zincProfile.py
while being in the top-level folder (idris2-chem)
Adjust the Settings below.
"""

from rdkit  import Chem
from typing import Iterable, List, Callable, Any, Tuple
import numpy as np
import time
import math
import psutil # Access to system resources

# Settings --------------------------------------------------------------------
path        = "resources/zinc.txt"
queries     = ["","CCC","C(=O)O"]
repetitions = 3

resultFile  = "resources/zincProfilingRDKit.txt"
delim       = ","

# Terminal color customization ------------------------------------------------
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

# Classes for data handling ---------------------------------------------------
# Note: Tried packing the lambda into a task class. Didn't work properly.

class ProfileResult:
    def __init__(self, name: str
                     , time: float
                     , runs: int
                     , res:  Any):
       self.name = name
       self.time = time
       self.runs = runs
       self.res  = res

    def averageTime(self) -> float:
        return self.time / self.runs

    def showTotalSeconds(self) -> str:
        return str(self.time) + " s"

    def showAverageSeconds(self) -> str:
        return str(self.averageTime()) + " s"

    def pretty(self) -> str:
        return "\n".join([ "\nTask:         " + self.name
                         , "Runs:         " + str(self.runs)
                         , "Total Time:   " + self.showTotalSeconds()
                         , "Average Time: " + self.showAverageSeconds()
                         , "Result:       " + str(self.res) + "\n" ])

    def showNoResult(self) -> str:
        return "\n".join([ "\nTask:         " + self.name
                         , "Runs:         " + str(self.runs)
                         , "Total Time:   " + self.showTotalSeconds()
                         , "Average Time: " + self.showAverageSeconds() ])


    def getRow(self) -> str:
        return delim.join([ self.name
                        , str(self.runs)
                        , self.showTotalSeconds()
                        , self.showAverageSeconds()
                        , str(self.res) ])


# Profiling functions ---------------------------------------------------------

def countMatches(query: Chem.rdchem.Mol, molList: Iterable[Chem.rdchem.Mol]) -> int:
    n = 0
    for t in molList:
        if t is None:
            print(f"{bcolors.WARNING}[Warning] countMatches: NoneType found!{bcolors.ENDC}")
        else:
            if t.HasSubstructMatch(query): n = n + 1;
    return n


def repeat(f: Callable[[None],Any],count: int) -> Any:
    i = 1; # Start at count 1 to skip the one which will be used to return
           # The return value
    while i < count:
        f()
        i = i + 1
    return f()


def runTask(name: str, task: Callable[[None],Any], runs: int) -> ProfileResult:
    start = time.time()
    res   = repeat(task,runs)
    end   = time.time()
    return ProfileResult(name, end - start, runs, res)



# Reporting of system resources


def reportSystemUsage() -> str:
    """
    Note: Read the docs about what the individual values mean
          https://psutil.readthedocs.io/en/latest/
    """
    mem = psutil.virtual_memory()
    prc = psutil.Process()
    prcmem = prc.memory_info()
    return "\n".join([ ""
                     # , "Memory used      / MB: " + str(mem.used / 1000000)
                     # , "Memory free      / MB: " + str(mem.free / 1000000)
                     # , "Memory active    / MB: " + str(mem.active / 1000000)
                     # , "Memory inactive  / MB: " + str(mem.inactive / 1000000)
                     # , "Memory shared    / MB: " + str(mem.shared / 1000000)
                     , "Process name               :  " + prc.name()
                     , "Process threads            :  " + str(prc.num_threads())
                     , "Process memory         / MB:  " + str(prcmem.rss / 1000000)
                     , "Process memor percent  /  %:  " +"%.2f" % round(prc.memory_percent() * 100,2)
                     , "Process virtual memory / MB:  " + str(prcmem.vms / 1000000)
                     , "Process shared memory  / MB:  " + str(prcmem.shared / 1000000)
                     , "Memory devoted to code / MB:  " + str(prcmem.text / 1000000)
                     , "CPU average load (1 min, 5 min, 15 min):" + str(psutil.getloadavg())
                     ])

# File Parsing ----------------------------------------------------------------
def getZincSMILES(path: str) -> List[str]:
    with open(path,'r') as fh:
      smilesList = fh.readlines()
      fh.close()
    return smilesList

def getZincMolecules(path: str) -> Iterable[Chem.rdchem.Mol]:
    ls = getZincSMILES(path)
    return map(Chem.MolFromSmiles,ls)

def measureGetZincMolecules(path: str) -> Iterable[Chem.rdchem.Mol]:
    print(f"{bcolors.OKGREEN}\n[Info] Loading ZINC molecules{bcolors.ENDC}")
    f        = lambda: list(getZincMolecules(path)) # A list dramatically increases matching speed after (iterable probably)
    pRes     = runTask('ZINC parsing',f,1)
    print(pRes.showNoResult())
    print(f"{bcolors.OKGREEN}\n[Info] Molecules loaded{bcolors.ENDC}")
    return pRes.res

# Write results to a file -----------------------------------------------------
def writeResults(path: str, result: ProfileResult):
    f = open(path, "a")
    f.write(result.getRow() + "\n")
    f.close()
    return


# Profiling functions ---------------------------------------------------------
def profile( queries:     Iterable[str]
           , path:        str
           , repetitions: int):


    print(reportSystemUsage())
    # Read molecules from file
    targets = measureGetZincMolecules(path)
    print(reportSystemUsage())
    # Clear contents of result file
    open(resultFile, 'w').close()

    # Profile queries
    print(f"{bcolors.OKGREEN}\n[Info] Starting profiling\n{bcolors.ENDC}")
    for query in queries:
      # Parse query and create executable function
      qry = Chem.MolFromSmiles(query)
      print('Searching matches for query: ',query)
      f   = lambda: countMatches(qry,targets)
      res = runTask(query,f,repetitions)
      print(res.pretty())
      # Write to file
      writeResults(resultFile,res)

    print(reportSystemUsage())
    return


# Execution -------------------------------------------------------------------
# Parsing takes a lot of time
# Measure time only for substructure search
print('--------- RDKit profiling ---------')
profile(queries,path, repetitions)
