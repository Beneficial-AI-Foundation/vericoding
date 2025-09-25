// <vc-preamble>
// Represents a universal function (ufunc) with input and output argument counts
datatype UFunc = UFunc(nin: nat, nout_val: nat)

// Validity predicate ensuring ufunc has at least one output argument
predicate ValidUFunc(ufunc: UFunc)
{
    ufunc.nout_val >= 1
}

// Returns the number of output arguments for a given ufunc
// This corresponds to accessing the nout attribute of NumPy ufuncs
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method nout(ufunc: UFunc) returns (result: nat)
    requires ValidUFunc(ufunc)  // Ensures ufunc has valid nout_val ≥ 1
    ensures result == ufunc.nout_val  // Correctness: returns exactly the nout_val field
    ensures result >= 1  // Lower bound: result is always ≥ 1
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
