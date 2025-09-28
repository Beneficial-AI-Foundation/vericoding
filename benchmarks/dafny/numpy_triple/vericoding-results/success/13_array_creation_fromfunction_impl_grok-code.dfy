// <vc-preamble>
// Function type that maps indices to real values
// Note: f will only be called with indices in range [0, n)
type IndexFunction = nat -> real

// Construct a vector by executing a function over each coordinate index
// Creates a vector of length n where element i is f(i)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added recursive helper function to build the sequence */
function Helper(n: nat, f: IndexFunction): seq<real>
  ensures |Helper(n, f)| == n
  ensures forall i :: 0 <= i < n ==> Helper(n, f)[i] == f(i)
{
  if n == 0 then []
  else Helper(n-1, f) + [f(n-1)]
}
// </vc-helpers>

// <vc-spec>
method fromfunction(n: nat, f: IndexFunction) returns (result: seq<real>)
  requires n >= 0
  ensures |result| == n
  ensures forall i :: 0 <= i < n ==> result[i] == f(i)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Call the recursive helper function to build the sequence */
  result := Helper(n, f);
}
// </vc-code>
