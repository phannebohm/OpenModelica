### new config flags

ODEJacobianMethod (default numeric), DAEJacobianMethod (default numeric), LSJacobianMethod (default symbolic), NLSJacobianMethod (default symbolic)
- none (no extra code generated, solver generates jacobian internally if needed)
- numeric (only generate sparsity pattern)
- symbolic (generate symbolic derivatives and sparsity pattern)

JacobianMethod (default default)
- default (uses settings from ODEJacobianMethod, DAEJacobianMethod, LSJacobianMethod, NLSJacobianMethod)
- none (no extra code generated, solver generates jacobian internally if needed)
- numeric (only generate sparsity pattern)
- symbolic (generate symbolic derivatives and sparsity pattern)

### new dump flags

-d=JacobianDump
-d=JacobianDumpV
