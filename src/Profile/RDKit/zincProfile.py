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
queries     = ["c1ccccc1.Cl","c1ccccc1.[Cl-]","c1ccccc1Cl"]
targets     = ["c1ccc(cc1)Cl","c1ccc(cc1)CCl","c1ccc(cc1)[N+]#N.[Cl-]"]
repetitions = 10
repForTrgs  = 100000

resultFile  = "resources/zincProfilingRDKit.txt"
delim       = ";"

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

def parseTargetMolecules(trgs : Iterable[str]) -> Iterable[Chem.rdchem.Mol]:
    """ Requires a list of targets"""
    return list(map(Chem.MolFromSmiles,trgs))


# Write results to a file -----------------------------------------------------
def writeResults(path: str, result: ProfileResult):
    f = open(path, "a")
    f.write(result.getRow() + "\n")
    f.close()
    return


# Profiling functions ---------------------------------------------------------
def profileZinc( queries:     Iterable[str]
               , path:        str
               , repetitions: int):

    # Print system usage - Initial
    #print(reportSystemUsage())
    print("Process name               :  " + psutil.Process().name())
    print("Process threads            :  " + str(psutil.Process().num_threads()))
    print("Process memory         / MB:  ")
    print(psutil.Process().memory_info().rss / 1000000)
    print("Process memory percent /  %:  ")
    print("%.2f" % round(psutil.Process().memory_percent() * 100,2))
    print("Process virtual memory / MB:  ")
    print(psutil.Process().memory_info().vms / 1000000)
    print("Process shared memory  / MB:  ")
    print(psutil.Process().memory_info().shared / 1000000)
    print("Memory devoted to code / MB:  ")
    print(psutil.Process().memory_info().text / 1000000)
    print("CPU average load (1 min, 5 min, 15 min):")
    print(psutil.getloadavg())
    targets = measureGetZincMolecules(path)
    #print(reportSystemUsage())
    print("Process memory         / MB:  ")
    print(psutil.Process().memory_info().rss / 1000000)
    print("Process memory percent /  %:  ")
    print("%.2f" % round(psutil.Process().memory_percent() * 100,2))
    print("Process virtual memory / MB:  ")
    print(psutil.Process().memory_info().vms / 1000000)
    print("Process shared memory  / MB:  ")
    print(psutil.Process().memory_info().shared / 1000000)
    print("Memory devoted to code / MB:  ")
    print(psutil.Process().memory_info().text / 1000000)
    print("CPU average load (1 min, 5 min, 15 min):")
    print(psutil.getloadavg())
    print("")

    # Read molecules from file
    # targets = measureGetZincMolecules(path)
    # print(reportSystemUsage())

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

       # System usage reports do not work when placed in an external function
       # (return always the same values)
       print("Process memory         / MB:  ")
       print(psutil.Process().memory_info().rss / 1000000)
       print("Process memory percent /  %:  ")
       print("%.2f" % round(psutil.Process().memory_percent() * 100,2))
       print("Process virtual memory / MB:  ")
       print(psutil.Process().memory_info().vms / 1000000)
       print("Process shared memory  / MB:  ")
       print(psutil.Process().memory_info().shared / 1000000)
       print("Memory devoted to code / MB:  ")
       print(psutil.Process().memory_info().text / 1000000)
       print("CPU average load (1 min, 5 min, 15 min):")
       print(psutil.getloadavg())
       print("")
    return



def profileTargets( queries:     Iterable[str]
                  , targets:     Iterable[str]
                  , repetitions: int):

    # Parsing & display system parameters
    print("Process name               :  " + psutil.Process().name())
    print("Process threads            :  " + str(psutil.Process().num_threads()))
    print("Process memory         / MB:  ")
    print(psutil.Process().memory_info().rss / 1000000)
    print("Process memory percent /  %:  ")
    print("%.2f" % round(psutil.Process().memory_percent() * 100,2))
    print("Process virtual memory / MB:  ")
    print(psutil.Process().memory_info().vms / 1000000)
    print("Process shared memory  / MB:  ")
    print(psutil.Process().memory_info().shared / 1000000)
    print("Memory devoted to code / MB:  ")
    print(psutil.Process().memory_info().text / 1000000)
    print("CPU average load (1 min, 5 min, 15 min):")
    print(psutil.getloadavg())
    trgs = parseTargetMolecules(targets)
    #print(reportSystemUsage())
    print("Process memory         / MB:  ")
    print(psutil.Process().memory_info().rss / 1000000)
    print("Process memory percent /  %:  ")
    print("%.2f" % round(psutil.Process().memory_percent() * 100,2))
    print("Process virtual memory / MB:  ")
    print(psutil.Process().memory_info().vms / 1000000)
    print("Process shared memory  / MB:  ")
    print(psutil.Process().memory_info().shared / 1000000)
    print("Memory devoted to code / MB:  ")
    print(psutil.Process().memory_info().text / 1000000)
    print("CPU average load (1 min, 5 min, 15 min):")
    print(psutil.getloadavg())
    print("")


    # Profile queries
    print(f"{bcolors.OKGREEN}\n[Info] Profiling individual Results\n{bcolors.ENDC}")

    # Display the individual results
    for query in queries:
       # Parse query and create executable function
       qry = Chem.MolFromSmiles(query)
       print('Searching matches for query: ',query)

       for i in range(len(trgs)):
         f   = lambda: trgs[i].HasSubstructMatch(qry)
         res = runTask(query + " -> " + targets[i],f,repetitions)

         print(res.pretty())
         # Write to file
         writeResults(resultFile,res)

       print(f"{bcolors.OKGREEN}\n[Info] System statistics\n{bcolors.ENDC}")
       # System usage reports do not work when placed in an external function
       # (return always the same values)
       print("Process memory         / MB:  ")
       print(psutil.Process().memory_info().rss / 1000000)
       print("Process memory percent /  %:  ")
       print("%.2f" % round(psutil.Process().memory_percent() * 100,2))
       print("Process virtual memory / MB:  ")
       print(psutil.Process().memory_info().vms / 1000000)
       print("Process shared memory  / MB:  ")
       print(psutil.Process().memory_info().shared / 1000000)
       print("Memory devoted to code / MB:  ")
       print(psutil.Process().memory_info().text / 1000000)
       print("CPU average load (1 min, 5 min, 15 min):")
       print(psutil.getloadavg())
       print("")


    print(f"{bcolors.OKGREEN}\n[Info] Profiling accumulated matches\n{bcolors.ENDC}")
    # Count the matches
    for query in queries:
       # Parse query and create executable function
       qry = Chem.MolFromSmiles(query)
       print('Searching matches for query: ',query)
       f   = lambda: countMatches(qry,trgs)
       res = runTask(query,f,repetitions)
       print(res.pretty())
       # Write to file
       writeResults(resultFile,res)

    print("Matched targets:")
    print(targets)
    return

# Execution -------------------------------------------------------------------
# Parsing takes a lot of time
# Measure time only for substructure search
print('--------- RDKit profiling ---------')
# Empty result file
open(resultFile, 'w').close()

#profileZinc(queries, path, repetitions)
#profileZinc(queries, path, repetitions)
#profileZinc(queries, path, repetitions)
#profileZinc(queries, path, repetitions)
#profileZinc(queries, path, repetitions)
#profileZinc(queries, path, repetitions)
#profileZinc(queries, path, repetitions)
#profileZinc(queries, path, repetitions)
#profileZinc(queries, path, repetitions)
#profileZinc(queries, path, repetitions)
profileTargets(queries, targets, repForTrgs)
