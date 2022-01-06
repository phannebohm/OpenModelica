/* Initialization */
#include "multary_simplification_model.h"
#include "multary_simplification_11mix.h"
#include "multary_simplification_12jac.h"
#if defined(__cplusplus)
extern "C" {
#endif


int multary_simplification_functionInitialEquations(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH

  data->simulationInfo->discreteCall = 1;
  data->simulationInfo->discreteCall = 0;

  TRACE_POP
  return 0;
}

/* No multary_simplification_functionInitialEquations_lambda0 function */

int multary_simplification_functionRemovedInitialEquations(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH
  const int *equationIndexes = NULL;
  double res = 0.0;


  TRACE_POP
  return 0;
}


#if defined(__cplusplus)
}
#endif

