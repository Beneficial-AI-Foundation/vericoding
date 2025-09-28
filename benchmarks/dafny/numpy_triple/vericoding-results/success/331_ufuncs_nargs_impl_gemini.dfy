// <vc-preamble>
// Structure representing a NumPy universal function (ufunc) with its metadata
datatype Ufunc = Ufunc(
    nin: nat,   // Number of input arguments the ufunc accepts
    nout: nat   // Number of output arguments the ufunc produces
)

// Returns the total number of arguments the ufunc accepts (nin + nout)
// This is a read-only attribute that provides metadata about the ufunc's signature
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_nargs(ufunc: Ufunc) returns (result: nat)
    ensures result == ufunc.nin + ufunc.nout
// </vc-spec>
// <vc-code>
{
  result := ufunc.nin + ufunc.nout;
}
// </vc-code>
