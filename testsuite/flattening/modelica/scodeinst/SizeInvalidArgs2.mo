// name: SizeInvalidArgs2
// keywords: size
// status: incorrect
//
// Tests the builtin size operator.
//

model SizeInvalidArgs2
  Real x[3];
  Integer y = size(x, dim = 1);
end SizeInvalidArgs2;

// Result:
// Error processing file: SizeInvalidArgs2.mo
// [flattening/modelica/scodeinst/SizeInvalidArgs2.mo:10:3-10:31:writable] Error: Function size has no input parameter named dim.
//
// # Error encountered! Exiting...
// # Please check the error message and the flags.
//
// Execution failed!
// endResult
