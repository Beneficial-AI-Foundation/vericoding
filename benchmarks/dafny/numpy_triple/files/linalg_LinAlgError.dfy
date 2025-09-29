// <vc-preamble>
// Linear algebra error type representing various failure conditions
datatype LinAlgError = 
  | NonConvergence(message: string)        // Numerical algorithm fails to converge
  | SingularMatrix(message: string)        // Matrix is singular (non-invertible)
  | NonSquareMatrix(message: string)       // Operation requires square matrix but input is not square
  | IncompatibleDimensions(message: string) // Matrix dimensions are incompatible for the operation
  | InvalidInput(message: string)          // Input parameters are invalid
  | NumericalInstability(message: string)  // Numerical computation becomes unstable
  | Other(message: string)                 // Generic error for other linear algebra failures

// Optional type for error results
datatype Option<T> = None | Some(value: T)

// Error checking predicate for linear algebra operations
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CheckLinAlgError(condition: bool, errorType: (string) -> LinAlgError, message: string) returns (result: Option<LinAlgError>)
  ensures condition ==> result == Some(errorType(message))
  ensures !condition ==> result == None
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
