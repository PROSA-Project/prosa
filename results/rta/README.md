# Verified Response-Time Analysis

The module `prosa.results.rta` collects all response-time analyses (RTAs) that have been verified with PROSA. 

## Organization 

This module is organized hierarchically as follows: 

1. the top-level modules (`ideal`, `rs`, etc.) represent different processor-model assumptions;
2. the second-level modules (`edf`, `fp`, `fifo`, etc.) represent different scheduling polices; and
3. the third-level modules (`fully_preemptive`, `limited_preemptive`, etc.) represent different preemption-model assumptions and further specific assumptions about the analyzed system model.

For example, the module `prosa.results.rta.ideal.fifo.bounded_nps` provides an RTA for tasks with bounded non-preemptive sections on ideal uniprocessors under FIFO scheduling.

## Processor Models

Currently, PROSA provides RTAs for the following processor models:

- `ideal` — ideal uniprocessors;
- `ovh` — non-ideal uniprocessors subject to scheduling overheads;
- `exc` — ideal uniprocessors subject to execution-time exceedance, as introduced by [Zini et al. (RTSS 2024)](https://doi.org/10.1109/RTSS62706.2024.00028);
- `prm` — the uniprocessor _periodic resource model_ due to [Shin & Lee (RTSS 2003)](https://doi.org/10.1109/REAL.2003.1253249);
- `arm` — the uniprocessor _average resource model_, also known as the _delay-rate model_ due to [Mok et al. (RTAS 2001)](https://doi.org/10.1109/RTTAS.2001.929867);
- `rs` — restricted-supply uniprocessors characterized by arbitrary _supply-bound functions_ (SBFs).


