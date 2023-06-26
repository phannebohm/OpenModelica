### new config flags

JacobianMethod (default default)
- default (uses settings from ODEJacobianMethod, DAEJacobianMethod, ...)
- none (no extra code generated, solver generates jacobian internally if needed)
- numeric (only generate sparsity pattern)
- symbolic (generate symbolic derivatives and sparsity pattern)

ODEJacobianMethod (default numeric),    "jacobian method for the ODE solver"
DAEJacobianMethod (default numeric),    "jacobian method for the DAE solver"
LSJacobianMethod  (default numeric),    "jacobian method for linear systems"
NLSJacobianMethod (default symbolic),    "jacobian method for nonlinear systems"
DIRJacobianMethod (default symbolic),    "jacobian method for dynamic index reduction"
LINJacobianMethod (default symbolic),    "jacobian method for linearization"
DRCJacobianMethdo (default symbolic)    "jacobian method for data reconciliation"
- none (no extra code generated, solver generates jacobian internally if needed)
- numeric (only generate sparsity pattern)
- symbolic (generate symbolic derivatives and sparsity pattern)

### new dump flags

-d=JacobianDump
-d=JacobianDumpV
