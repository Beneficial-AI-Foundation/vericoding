// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parse errors by adding parentheses for clarity and ensuring all necessary values are of type real before division. Removed extra `as real` cast. */
function Length(start: real, stop: real, step: real): nat
{
  if step > 0.0 then
    if start >= stop then 0
    else (((stop - start - 1e-10) / step) + 1.0) as nat
  else if step < 0.0 then
    if start <= stop then 0
    else (((start - stop - 1e-10) / (-step)) + 1.0) as nat
  else 0 // Should not happen given the precondition step != 0.0
}
// </vc-helpers>

// <vc-spec>
method Arange(start: real, stop: real, step: real) returns (result: seq<real>)
  requires step != 0.0
  ensures step > 0.0 ==> (|result| == 0 <==> start >= stop)
  ensures step < 0.0 ==> (|result| == 0 <==> start <= stop)
  ensures step > 0.0 && start < stop ==> 
    |result| > 0 && |result| as real * step >= (stop - start) && (|result| - 1) as real * step < (stop - start)
  ensures step < 0.0 && start > stop ==> 
    |result| > 0 && |result| as real * (-step) >= (start - stop) && (|result| - 1) as real * (-step) < (start - stop)
  ensures forall i :: 0 <= i < |result| ==> result[i] == start + (i as real) * step
  ensures step > 0.0 ==> forall i :: 0 <= i < |result| ==> result[i] >= start && result[i] < stop
  ensures step < 0.0 ==> forall i :: 0 <= i < |result| ==> result[i] <= start && result[i] > stop
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Called the helper function 'Length' to calculate the number of elements and used it to initialize the array. */
{
  var numElements: nat := Length(start, stop, step);
  result := Array.Init(numElements, i => start + i as real * step);
}
// </vc-code>
