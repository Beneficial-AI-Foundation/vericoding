// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function ComputeStep(start: real, stop: real, n: nat): real
  requires n > 1
{
  (stop - start) / ((n - 1) as real)
}

function ComputeValue(start: real, step: real, i: int): real
{
  start + (i as real) * step
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
    result := [start];
  } else {
    var step := ComputeStep(start, stop, n);
    result := seq(n, i requires 0 <= i < n => ComputeValue(start, step, i));
  }
}
// </vc-code>
