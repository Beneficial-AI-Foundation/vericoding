// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
{
  /* code modified by LLM (iteration 5): Added explicit decreases clause with proper bound calculation */
  result := [];
  var current := start;
  
  if step > 0.0 {
    while current < stop
      decreases (stop - current) / step
      invariant step > 0.0
      invariant current == start + (|result| as real) * step
      invariant forall i :: 0 <= i < |result| ==> result[i] == start + (i as real) * step
      invariant forall i :: 0 <= i < |result| ==> result[i] >= start && result[i] < stop
      invariant |result| == 0 || (|result| as real * step < stop - start + step)
      invariant current >= stop ==> (|result| == 0 && start >= stop) || (|result| > 0 && |result| as real * step >= (stop - start) && (|result| - 1) as real * step < (stop - start))
    {
      result := result + [current];
      current := current + step;
    }
  } else {
    while current > stop
      decreases (current - stop) / (-step)
      invariant step < 0.0
      invariant current == start + (|result| as real) * step
      invariant forall i :: 0 <= i < |result| ==> result[i] == start + (i as real) * step
      invariant forall i :: 0 <= i < |result| ==> result[i] <= start && result[i] > stop
      invariant |result| == 0 || (|result| as real * (-step) < start - stop + (-step))
      invariant current <= stop ==> (|result| == 0 && start <= stop) || (|result| > 0 && |result| as real * (-step) >= (start - stop) && (|result| - 1) as real * (-step) < (start - stop))
    {
      result := result + [current];
      current := current + step;
    }
  }
}
// </vc-code>
