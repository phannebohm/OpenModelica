/* Simulation code for multary_simplification generated by the OpenModelica Compiler OMCompiler v1.19.0-dev.415+g6cd5c98f92. */
#if !defined(multary_simplification__MODEL_H)
#define multary_simplification__MODEL_H

#include "openmodelica.h"
#include "openmodelica_func.h"
#include "simulation_data.h"
#include "simulation/simulation_info_json.h"
#include "simulation/simulation_runtime.h"
#include "util/omc_error.h"
#include "util/parallel_helper.h"
#include "simulation/solver/model_help.h"
#include "simulation/solver/delay.h"
#include "simulation/solver/linearSystem.h"
#include "simulation/solver/nonlinearSystem.h"
#include "simulation/solver/mixedSystem.h"
#include "simulation/solver/spatialDistribution.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>

#include "multary_simplification_functions.h"


extern void multary_simplification_callExternalObjectDestructors(DATA *_data, threadData_t *threadData);
#if !defined(OMC_NUM_NONLINEAR_SYSTEMS) || OMC_NUM_NONLINEAR_SYSTEMS>0
#endif
#if !defined(OMC_NUM_LINEAR_SYSTEMS) || OMC_NUM_LINEAR_SYSTEMS>0
#endif
#if !defined(OMC_NUM_MIXED_SYSTEMS) || OMC_NUM_MIXED_SYSTEMS>0
#endif
#if !defined(OMC_NO_STATESELECTION)
extern void multary_simplification_initializeStateSets(int nStateSets, STATE_SET_DATA* statesetData, DATA *data);
#endif
extern int multary_simplification_functionAlgebraics(DATA *data, threadData_t *threadData);
extern int multary_simplification_function_storeDelayed(DATA *data, threadData_t *threadData);
extern int multary_simplification_function_storeSpatialDistribution(DATA *data, threadData_t *threadData);
extern int multary_simplification_function_initSpatialDistribution(DATA *data, threadData_t *threadData);
extern int multary_simplification_updateBoundVariableAttributes(DATA *data, threadData_t *threadData);
extern int multary_simplification_functionInitialEquations(DATA *data, threadData_t *threadData);
extern int multary_simplification_functionInitialEquations_lambda0(DATA *data, threadData_t *threadData);
extern int multary_simplification_functionRemovedInitialEquations(DATA *data, threadData_t *threadData);
extern int multary_simplification_updateBoundParameters(DATA *data, threadData_t *threadData);
extern int multary_simplification_checkForAsserts(DATA *data, threadData_t *threadData);
extern int multary_simplification_function_ZeroCrossingsEquations(DATA *data, threadData_t *threadData);
extern int multary_simplification_function_ZeroCrossings(DATA *data, threadData_t *threadData, double* gout);
extern int multary_simplification_function_updateRelations(DATA *data, threadData_t *threadData, int evalZeroCross);
extern const char* multary_simplification_zeroCrossingDescription(int i, int **out_EquationIndexes);
extern const char* multary_simplification_relationDescription(int i);
extern void multary_simplification_function_initSample(DATA *data, threadData_t *threadData);
extern int multary_simplification_initialAnalyticJacobianG(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *jacobian);
extern int multary_simplification_initialAnalyticJacobianA(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *jacobian);
extern int multary_simplification_initialAnalyticJacobianB(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *jacobian);
extern int multary_simplification_initialAnalyticJacobianC(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *jacobian);
extern int multary_simplification_initialAnalyticJacobianD(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *jacobian);
extern int multary_simplification_initialAnalyticJacobianF(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *jacobian);
extern int multary_simplification_functionJacG_column(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *thisJacobian, ANALYTIC_JACOBIAN *parentJacobian);
extern int multary_simplification_functionJacA_column(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *thisJacobian, ANALYTIC_JACOBIAN *parentJacobian);
extern int multary_simplification_functionJacB_column(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *thisJacobian, ANALYTIC_JACOBIAN *parentJacobian);
extern int multary_simplification_functionJacC_column(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *thisJacobian, ANALYTIC_JACOBIAN *parentJacobian);
extern int multary_simplification_functionJacD_column(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *thisJacobian, ANALYTIC_JACOBIAN *parentJacobian);
extern int multary_simplification_functionJacF_column(void* data, threadData_t *threadData, ANALYTIC_JACOBIAN *thisJacobian, ANALYTIC_JACOBIAN *parentJacobian);
extern const char* multary_simplification_linear_model_frame(void);
extern const char* multary_simplification_linear_model_datarecovery_frame(void);
extern int multary_simplification_mayer(DATA* data, modelica_real** res, short *);
extern int multary_simplification_lagrange(DATA* data, modelica_real** res, short *, short *);
extern int multary_simplification_pickUpBoundsForInputsInOptimization(DATA* data, modelica_real* min, modelica_real* max, modelica_real*nominal, modelica_boolean *useNominal, char ** name, modelica_real * start, modelica_real * startTimeOpt);
extern int multary_simplification_setInputData(DATA *data, const modelica_boolean file);
extern int multary_simplification_getTimeGrid(DATA *data, modelica_integer * nsi, modelica_real**t);
extern void multary_simplification_function_initSynchronous(DATA * data, threadData_t *threadData);
extern void multary_simplification_function_updateSynchronous(DATA * data, threadData_t *threadData, long clockIndex);
extern int multary_simplification_function_equationsSynchronous(DATA * data, threadData_t *threadData, long clockIndex);
extern void multary_simplification_read_input_fmu(MODEL_DATA* modelData, SIMULATION_INFO* simulationData);
extern void multary_simplification_function_savePreSynchronous(DATA *data, threadData_t *threadData);
extern int multary_simplification_inputNames(DATA* data, char ** names);
extern int multary_simplification_dataReconciliationInputNames(DATA* data, char ** names);
extern int multary_simplification_initializeDAEmodeData(DATA *data, DAEMODE_DATA*);
extern int multary_simplification_functionLocalKnownVars(DATA*, threadData_t*);
extern int multary_simplification_symbolicInlineSystem(DATA*, threadData_t*);

#include "multary_simplification_literals.h"




#if defined(HPCOM) && !defined(_OPENMP)
  #error "HPCOM requires OpenMP or the results are wrong"
#endif
#if defined(_OPENMP)
  #include <omp.h>
#else
  /* dummy omp defines */
  #define omp_get_max_threads() 1
#endif

#if defined(__cplusplus)
}
#endif

#endif /* !defined(multary_simplification__MODEL_H) */

