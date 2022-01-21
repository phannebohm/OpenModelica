/* Algebraic */
#include "multary_simplification_model.h"

#ifdef __cplusplus
extern "C" {
#endif


/* forwarded equations */
extern void multary_simplification_eqFunction_4(DATA* data, threadData_t *threadData);

static void functionAlg_system0(DATA *data, threadData_t *threadData)
{
  multary_simplification_eqFunction_4(data, threadData);
  threadData->lastEquationSolved = 4;
}

/* forwarded equations */
extern void multary_simplification_eqFunction_3(DATA* data, threadData_t *threadData);

static void functionAlg_system1(DATA *data, threadData_t *threadData)
{
  multary_simplification_eqFunction_3(data, threadData);
  threadData->lastEquationSolved = 3;
}
OMC_DISABLE_OPT
static void (*functionAlg_systems[2])(DATA *, threadData_t *threadData) = {
  functionAlg_system0,
  functionAlg_system1
};
/* for continuous time variables */
int multary_simplification_functionAlgebraics(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH
  int id;

#if !defined(OMC_MINIMAL_RUNTIME)
  if (measure_time_flag) rt_tick(SIM_TIMER_ALGEBRAICS);
#endif
  data->simulationInfo->callStatistics.functionAlgebraics++;

  for(id=0; id<2; id++) {
    functionAlg_systems[id](data, threadData);
  }

  multary_simplification_function_savePreSynchronous(data, threadData);

#if !defined(OMC_MINIMAL_RUNTIME)
  if (measure_time_flag) rt_accumulate(SIM_TIMER_ALGEBRAICS);
#endif

  TRACE_POP
  return 0;
}

#ifdef __cplusplus
}
#endif
