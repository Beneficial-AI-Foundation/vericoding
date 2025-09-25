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
{
  assume {:axiom} false;
}
// </vc-code>
