// <vc-preamble>
// Function type that maps indices to real values
// Note: f will only be called with indices in range [0, n)
type IndexFunction = nat -> real

// Construct a vector by executing a function over each coordinate index
// Creates a vector of length n where element i is f(i)
// </vc-preamble>

// <vc-helpers>
lemma ArraySliceFacts<T>(a: array<T>)
  ensures |a[..]| == a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[..][i] == a[i]
{
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
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == f(j)
  {
    a[i] := f(i);
    i := i + 1;
  }
  result := a[..];
}

// </vc-code>
