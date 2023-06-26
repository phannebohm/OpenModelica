
# Modules: (ignore these, just modules for OB)

calculateStateSetsJacobians

    (Generates analytical jacobian for dynamic state selection sets.)

calculateStrongComponentJacobians

    (Generates analytical jacobian for torn linear and non-linear strong components. By default linear components and non-linear components with user-defined function calls are skipped. See also debug flags: LSanalyticJacobian, NLSanalyticJacobian and forceNLSanalyticJacobian)

symbolicJacobian

    (Detects the sparse pattern of the ODE system and calculates also the symbolic Jacobian if flag '--generateSymbolicJacobian' is enabled.)


# Config Flags: (remove)

--generateSymbolicJacobian

    Generates symbolic Jacobian matrix, where der(x) is differentiated w.r.t. x. This matrix can be used by dassl or ida solver with simulation flag '-jacobian'.


# Debug Flags: (remove)

LSanalyticJacobian (default: off)

    Enables analytical jacobian for linear strong components. Defaults to false

NLSanalyticJacobian (default: on)

    Enables analytical jacobian for non-linear strong components without user-defined function calls, for that see forceNLSanalyticJacobian

disableJacsforSCC (default: off)

    Disables calculation of jacobians to detect if a SCC is linear or non-linear. By disabling all SCC will handled like non-linear.

forceNLSanalyticJacobian (default: off)

    Forces calculation analytical jacobian also for non-linear strong components with user-defined functions.

constjac (default: off) (module will be ASSC)

    solves linear systems with constant Jacobian and variable b-Vector symbolically

# Debug Flags: (keep or change)

symJacConstantSplit (default: off) (this should be always on and an option for the user to change doesnt make sense. activate flag generally and see if it works)

    Generates all symbolic Jacobians with splitted constant parts.


## (Debug Flags) Dumps: (remove for new flags)

debugAlgebraicLoopsJacobian (default: off)

    Dumps debug output while creating symbolic jacobians for non-linear systems.

dumpExcludedSymJacExps (default: off)

    This flags dumps all expression that are excluded from differentiation of a symbolic Jacobian.

symjacdump (default: off)

    Dumps information about symbolic Jacobians. Can be used only with postOptModules: generateSymbolicJacobian, generateSymbolicLinearization.

symjacdumpeqn (default: off)

    Dump for debug purpose of symbolic Jacobians. (deactivated now).

symjacdumpverbose (default: off)

    Dumps information in verbose mode about symbolic Jacobians. Can be used only with postOptModules: generateSymbolicJacobian, generateSymbolicLinearization.

symjacwarnings (default: off)

    Prints warnings regarding symoblic jacbians
