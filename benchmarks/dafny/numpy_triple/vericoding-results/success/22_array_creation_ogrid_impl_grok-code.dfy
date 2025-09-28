// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
{  // code modified by LLM (iteration 2): Implementing sequence construction with loop invariants for verifiable ensures
  var s: seq<real> := [];
  if n == 1 {
    s := [start];
  } else {
    var step: real := (stop - start) / ((n as real) - 1.0);
    var i: int := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |s| == i
      invariant n > 1 && forall j :: 0 <= j < i ==> s[j] == start + (j as real) * step
    {
      s := s + [start + (i as real) * step];
      i := i + 1;
    }
  }
  result := s;
}
// </vc-code>
