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
  /* code modified by LLM (iteration 5): fixed type mismatch in decreases clause by using 0.0 instead of 0 */
  var s: seq<real> := [];
  var current := start;
  while (step > 0.0 ==> current < stop) && (step < 0.0 ==> current > stop)
    decreases if step >0.0 then stop - current else if step <0.0 then current - stop else 0.0
    invariant |s| >= 0
    invariant current == start + (|s| as real) * step
    invariant forall i :: 0 <= i < |s| ==> s[i] == start + (i as real) * step
    invariant step > 0.0 ==> forall i :: 0 <= i < |s| ==> s[i] >= start && s[i] < stop
    invariant step < 0.0 ==> forall i :: 0 <= i < |s| ==> s[i] <= start && s[i] > stop
  {
    s := s + [current];
    current := current + step;
  }
  result := s;
}
// </vc-code>
