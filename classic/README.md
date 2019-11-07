# Classic Prosa

This module contains the Coq specification & proof development of the Prosa project as presented in the ECRTS'16 paper by Cerqueira et al. 

- Felipe Cerqueira, Felix Stutz, and Björn Brandenburg, “[Prosa: A Case for Readable Mechanized Schedulability Analysis](https://www.mpi-sws.org/~bbb/papers/pdf/ecrts16f.pdf)”, *Proceedings of the 28th Euromicro Conference on Real-Time Systems (ECRTS 2016)*, pp. 273–284, July 2016.

This "classic" version of Prosa has since been superseded by a restructuring and refactoring effort that took place throughout most of 2019 in the context of the [RT-Proofs project](https://rt-proofs.inria.fr/) (kindly funded jointly by ANR and DFG, projects ANR-17-CE25-0016 and DFG-391919384, respectively).

For the sake of historical completeness, and since not all "classic" proofs have (yet) been ported to the new Prosa base, "classic" Prosa is still included in the master branch of Prosa of the time being.

## Directory Structure

The Classic Prosa directory was intended to be organized in a hierarchy: while generic, reusable foundations stay in the upper levels, definitions for specific analyses may be found deeper in the directory tree. However, this organizational principle is not consistently followed due to historical developments. 

### Base Directories

Classic Prosa contains the following base directories:

- **classic/model/:** Specification of task and scheduler models, as well as generic lemmas related to scheduling.
	  
- **classic/analysis/:** Definition, proofs and implementation of schedulability analyses.

- **classic/implementation/:** Instantiation of each schedulability analysis with concrete task and scheduler implementations.  
Instantiating the main theorems in an assumption free environment shows the absence of contradictory assumptions in the proofs.

- **classic/util/:** additional helper lemmas, notations, and tactics that are no longer used in the "new Prosa".

### Internal Directories

The major concepts in classic Prosa are specified in the *classic/model/* folder.

- **classic/model/arrival:** Arrival sequences and arrival bounds
- **classic/model/schedule:** Definitions and properties of schedules

Inside *classic/model/schedule*, one can find the different classes of schedulers.

- **classic/model/schedule/uni:** Uniprocessor scheduling.
- **classic/model/schedule/global:** Global scheduling.
- **classic/model/schedule/partitioned:** Partitioned scheduling.
- **classic/model/schedule/apa:** APA scheduling.

For example, the schedulability analysis for global scheduling with release jitter is organized as follows.

- **classic/model/schedule/global/jitter:** Definitions and lemmas for global scheduling with release jitter.
- **classic/analysis/global/jitter:** Analysis for global scheduling with release jitter.
- **classic/implementation/global/jitter:** Implementation of the concrete scheduler with release jitter. 

## Extending Prosa

Please do not extend this classic version of Prosa in ongoing or future work. As of 2019, all efforts should now be focused on the new, restructured base.
