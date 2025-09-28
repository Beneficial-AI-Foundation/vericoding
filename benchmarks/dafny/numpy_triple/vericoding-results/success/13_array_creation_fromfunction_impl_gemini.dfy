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
  /* code modified by LLM (iteration 5): added invariant i <= n to help prove loop properties */
  var res: seq<real> := [];
  var i: nat := 0;
  while i < n
    invariant |res| == i
    invariant forall k :: 0 <= k < i ==> res[k] == f(k)
    invariant i <= n
    decreases n - i
  {
    res := res + [f(i)];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
