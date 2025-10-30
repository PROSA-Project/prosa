# Changelog

Starting after release v0.6, all notable changes to this project will be documented in this file.
Earlier changes were not documented in detail.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/).


## [0.6] — 2025-10-31

### Added

- Introduce a proper change log.
- Demand Bound Function (DBF) definition and lemmas.
- Restricted-supply ELF RTAs.
- RTA for non-sequential tasks under FP scheduling.
- Exceedance-aware RTA for NP-FP.
- Definition of ELF scheduling.
- Generality of ELF and GEL scheduling.
- Introduce abstract Restricted-Supply Analysis (aRSA).
- EDF, FP, and ELF RTAs for restricted-supply processors. 
- EDF and FP RTAs for overhead-affected processors. 
- EDF and FP RTAs for periodic and average resource models.
- Transfer schedulability theory. 

### Changed

- Converted ε to notation to avoid having to unfold it.
- Rewrote `create_makefile.sh` as a Makefile.
- Removed work-conservation dependency from the priority inversion file.


### Removed

- Classic Prosa is now in a separate branch. 


## [0.5] - 2022-11-07

See: <https://prosa.mpi-sws.org/releases/v0.5/index.html>

### Added

- First release on OPAM
- [POET](https://prosa.mpi-sws.org/poet.html) support 
- RTA for FIFO scheduling based on aRTA
- Definition of GEL scheduling
- RTA for GEL scheduling based on aRTA
- notion of hyperperiod for periodic tasks
- add utilities for finding fixpoints of functions 
- computed fixpoints for FP-FP RTA

### Changed

- no longer hard-coded ideal processor model in aRTA
- aRTA: relax `A + F = task_rtct + IBF A (A + F)` to `A + F >= task_rtct + IBF A (A + F)`
- generalized definition of busy interval
- replace ssrlia with mczify

## [0.4] - 2019-12-21

See: <https://prosa.mpi-sws.org/releases/v0.4/index.html>

### Added 

- preemption models
- abstract RTA (aRTA)
- aRTA instantiations for EDF and FP based on aRTA for four preemption models
    - fully preemptive
    - floating non-preemptive segments
    - segmented limited-preemptive
    - fully non-preemptive
- EDF optimality proof

### Changed

- pretty much everything, this was a complete refactoring of Prosa 

### Removed

The following results were removed because they were not ported to the new Prosa structure in time for the release.
The work lives on in the ["classic" Prosa](https://prosa.mpi-sws.org/results.html#resultsinclassicprosa) branch.

- sustainability theory
- RTA for TDMA scheduling
- RTA for FP scheduling with release jitter
- suspension-oblivious RTA for FP scheduling
- suspension-aware RTA for FP scheduling
- RTA for global EDF
- RTA for global FP
- APA scheduling


## [0.3] - 2018-07-17

See: <https://prosa.mpi-sws.org/releases/v0.3/index.html>

### Added

- strong and weak sustainability theory
- dynamic self-suspension model
- proof of weak sustainability w.r.t. job costs and variable suspension times of uniprocessor JLFP scheduling


## [0.2] - 2016-06-06

See: <https://prosa.mpi-sws.org/releases/v0.2/apa/index.html>

### Added 

- APA scheduling

## [0.1] - 2016-05-05

First public release of Prosa. 

See: <https://prosa.mpi-sws.org/releases/v0.1/artifact/index.html>




