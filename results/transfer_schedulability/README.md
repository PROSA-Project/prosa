# Rocq Proof of Transfer Schedulability

Transfer schedulability is a concept that allows mimicking the behavior of some reference schedule in an online schedule such that no job finishes later in the online schedule than in the reference schedule. This notion was first introduced in the following EMSOFT'25 paper:

- Willemsen et al., “[Transfer Schedulability in Periodic Real-Time Systems](https://doi.org/10.1145/3763236)”, EMSOFT 2025  / ACM TECS, October 2025.

This module was originally developed as supporting material for the above paper. In particular, the file [`prosa.results.transfer_schedulability.criterion`](criterion.v) provides mechanized proofs of three theorems related to the *transfer schedulability criterion*.

1. The transfer schedulability criterion w.r.t. *online* job costs is a **sufficient** condition for schedulability to be transferred.
2. The transfer schedulability criterion w.r.t. *online* job costs is a **necessary** condition for schedulability to be transferred.
3. The transfer schedulability criterion w.r.t. *reference* job costs is a **sufficient** condition for schedulability to be transferred.

Additionally, the file [`prosa.results.transfer_schedulability.paper_model`](paper_model.v) elaborates how the above mechanized general theorems relate to the more specialized model assumed in the paper.

Please see the paper for a more elaborate introduction to the transfer schedulability concept and its potential applications.
