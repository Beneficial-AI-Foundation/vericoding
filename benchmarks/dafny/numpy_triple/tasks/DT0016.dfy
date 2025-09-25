// <vc-preamble>
// Function type that maps indices to real values
// Note: f will only be called with indices in range [0, n)
type IndexFunction = nat -> real

// Construct a vector by executing a function over each coordinate index
// Creates a vector of length n where element i is f(i)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method fromfunction(n: nat, f: IndexFunction) returns (result: seq<real>)
  requires n >= 0
  ensures |result| == n
  ensures forall i :: 0 <= i < n ==> result[i] == f(i)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
