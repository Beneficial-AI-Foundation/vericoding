// <vc-preamble>
// External logarithm function declaration
function {:extern} Log(x: real): real
  requires x > 0.0
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method log(x: array<real>) returns (result: array<real>)
  // Precondition: All elements must be positive
  requires forall i :: 0 <= i < x.Length ==> x[i] > 0.0
  
  // Postcondition: Result has same length and each element is log of corresponding input element
  ensures result.Length == x.Length
  ensures forall i :: 0 <= i < result.Length ==> result[i] == Log(x[i])
// </vc-spec>
// <vc-code>
{
  var n := x.Length;
  var r := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r.Length == n
    invariant forall k :: 0 <= k < i ==> r[k] == Log(x[k])
    decreases n - i
  {
    assert 0 <= i < x.Length;
    assert x[i] > 0.0;
    r[i] := Log(x[i]);
    i := i + 1;
  }
  result := r;
}
// </vc-code>
