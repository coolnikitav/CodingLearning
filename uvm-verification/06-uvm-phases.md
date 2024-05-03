# UVM_PHASES

## Fundamentals of Phases
- Q: What do phases handle?
- A:
  - Configure TB env
  - System Reset
  - Applying stimulus to DUT
  - Comparing Response with golden data
  - Generating report

## Classification of Phases: Methods Used
- Q: Give example of a phase that consumes time. The doesn't consume time
  
- Phases
  - Consume time
    - Task
  - Do not consume time
    - Function, super
 
- A: Does not consume time: creating object or class. This method should not consume time to make sure all objects are ready at 0 nSec
- A: Consumes times: applying stimulus to DUT on valid clock edge. If we apply all the stimulus at 0 nSec, we will get unexpected behavior.

## Classification of Phases: Specific Purposes
- Q: What are the 3 types of phases? Give at least 2 examples of each type.

- Phase
  - Construction phase
    - build_phase - create object of a class
    - connect_phase - perform connection of a component in a TLM (transaction-level modeling)
    - end_of_elaboration_phase - adjust hierarchy of a component
    - start_of_simulation - configure env before applying stimulus
  - run_phase - generation and application of stimulus, waiting for results
    - reset_phase, pre_reset_phase, post_reset_phase - system reset
    - configure_phase, pre_configure_phase, post_configure_phase - set variables to certain values before generation
    - main_phase, pre_main_phase, post_main_phase - generating stimulus + collecting response
    - shutdown_phase, pre_shutdown_phase, post_shutdown_phase - make sure that all stimuli is correctly applied to the DUT and got a response
  - cleanup phase - collect and report data, check that coverage goals are achieved
    - extract_phase
    - check_phase
    - report_phase
    - final_phase
