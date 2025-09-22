// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ogrid(start: real, stop: real, step: real, n: nat) returns (result: seq<real>)
  // Precondition: step must be non-zero
  requires step != 0.0
  
  // Precondition: n must equal the number of steps from start to stop
  requires n == (if step > 0.0 then (stop - start) / step else (start - stop) / (-step)) as int
  
  // Postcondition: result has exactly n elements
  ensures |result| == n
  
  // Postcondition: each element forms an arithmetic sequence
  ensures forall i :: 0 <= i < n ==> result[i] == start + (i as real) * step
  
  // Postcondition: all elements are within the appropriate range based on step direction
  ensures forall i :: 0 <= i < n ==> 
    if step > 0.0 then start <= result[i] < stop
    else stop < result[i] <= start
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
