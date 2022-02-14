/* Initialization */
#include "multary_simplification_model.h"
#include "multary_simplification_11mix.h"
#include "multary_simplification_12jac.h"
#if defined(__cplusplus)
extern "C" {
#endif

void multary_simplification_functionInitialEquations_0(DATA *data, threadData_t *threadData);

/*
equation index: 1
type: SIMPLE_ASSIGN
z = 5.0 * time
*/
void multary_simplification_eqFunction_1(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH
  const int equationIndexes[2] = {1,1};
  data->localData[0]->realVars[0] /* z variable */ = (5.0) * (data->localData[0]->timeValue);
  TRACE_POP
}
OMC_DISABLE_OPT
void multary_simplification_functionInitialEquations_0(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH
  multary_simplification_eqFunction_1(data, threadData);
  TRACE_POP
}

int multary_simplification_functionInitialEquations(DATA *data, threadData_t *threadData)
{
  TRACE_PUSH

  data->simulationInfo->discreteCall = 1;
  multary_simplification_functionInitialEquations_0(data, threadData);
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

