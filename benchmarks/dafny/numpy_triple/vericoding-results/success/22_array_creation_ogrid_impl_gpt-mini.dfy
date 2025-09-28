// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function value_at(start: real, stop: real, n: nat, i: int): real
  requires n > 1 && 0 <= i < n
{
  start + (i as real) * ((stop - start) / ((n - 1) as real))
}
// </vc-helpers>

// <vc-spec>
method ogrid(start: real, stop: real, n: nat) returns (result: seq<real>)
  // Precondition: must have at least one point
  requires n > 0
  // Postcondition: result has exactly n elements
  ensures |result| == n
  // For single element case, it equals start
  ensures n == 1 ==> result[0] == start
  // For multiple elements, they are evenly spaced from start to stop
  ensures n > 1 ==> (forall i :: 0 <= i < n ==> 
    result[i] == start + (i as real) * ((stop - start) / ((n - 1) as real)))
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    var a := new real[1];
    a[0] := start;
    result := a[..];
  } else {
    var step := (stop - start) / ((n - 1) as real);
    var a := new real[n];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant forall j :: 0 <= j < i ==> a[j] == start + (j as real) * step
    {
      a[i] := start + (i as real) * step;
      i := i + 1;
    }
    result := a[..];
  }
}
// </vc-code>
