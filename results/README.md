# PROSA Results Module

This module collects PROSA's high-level mechanized results. It serves a dual purpose: 

1. to provide theorems for reuse in other developments that need schedulability analysis results (i.e., this is the main interface of PROSA as a Rocq library), 
2. to provide a human-friendly reference specification of verified results one may want to reuse as building blocks in non-mechanized research papers.

The following categories are currently provided: 

- [`prosas.results.rta`](./rta/README.md) — all response-time analyses currently verified in PROSA;
- `prosas.results.generality` — statements about the hierarchy of scheduling policies (currently GEL and ELF);
- `prosas.results.optimality` — optimality results (currently only EDF); and
- [`prosas.results.transfer_schedulability`](./transfer_schedulability/README.md) — scheduling-theoretic results about transferring timeliness guarantees from one schedule to another.
