// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retained ValAt function for mapping indices to values */
function ValAt(start: real, step: real, i: int): real
  requires i >= 0
{
  start + (i as real) * step
}

/* helper modified by LLM (iteration 5): lemma to relate length and bounds for positive step */
lemma LemmaBoundsPositive(start: real, stop: real, step: real, k: int)
  requires step > 0.0
  requires start < stop
  requires k > 0
  requires start + (k as real) * step >= stop
  requires start + ((k - 1) as real) * step < stop
  ensures (k as real) * step >= (stop - start)
  ensures ((k - 1) as real) * step < (stop - start)
{
  assert (k as real) * step >= stop - start;
  assert ((k - 1) as real) * step < stop - start;
}

/* helper modified by LLM (iteration 5): lemma to relate length and bounds for negative step */
lemma LemmaBoundsNegative(start: real, stop: real, step: real, k: int)
  requires step < 0.0
  requires start > stop
  requires k > 0
  requires start + (k as real) * step <= stop
  requires start + ((k - 1) as real) * step > stop
  ensures (k as real) * (-step) >= (start - stop)
  ensures ((k - 1) as real) * (-step) < (start - stop)
{
  assert -step > 0.0;
  assert (k as real) * (-step) >= start - stop;
  assert ((k - 1) as real) * (-step) < start - stop;
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
{
  /* code modified by LLM (iteration 5): ensure loop termination via real-valued decreases and initialize accumulator with first element */
  if step > 0.0 {
    if start < stop {
      var acc: seq<real> := [start];
      var x: real := start + step;
      while x < stop
        invariant step > 0.0
        invariant x == start + (|acc| as real) * step
        invariant forall i :: 0 <= i < |acc| ==> acc[i] == start + (i as real) * step
        invariant forall i :: 0 <= i < |acc| ==> acc[i] >= start && acc[i] < stop
        decreases if x < stop then stop - x else 0.0
      {
        acc := acc + [x];
        x := x + step;
      }
      result := acc;
      assert x >= stop;
      assert x == start + (|result| as real) * step;
      assert |result| > 0;
      assert result[|result|-1] == start + ((|result|-1) as real) * step;
      assert result[|result|-1] < stop;
      LemmaBoundsPositive(start, stop, step, |result|);
    } else {
      result := [];
    }
  } else {
    if start > stop {
      var acc: seq<real> := [start];
      var x: real := start + step;
      while x > stop
        invariant step < 0.0
        invariant x == start + (|acc| as real) * step
        invariant forall i :: 0 <= i < |acc| ==> acc[i] == start + (i as real) * step
        invariant forall i :: 0 <= i < |acc| ==> acc[i] <= start && acc[i] > stop
        decreases if x > stop then x - stop else 0.0
      {
        acc := acc + [x];
        x := x + step;
      }
      result := acc;
      assert x <= stop;
      assert x == start + (|result| as real) * step;
      assert |result| > 0;
      assert result[|result|-1] == start + ((|result|-1) as real) * step;
      assert result[|result|-1] > stop;
      LemmaBoundsNegative(start, stop, step, |result|);
    } else {
      result := [];
    }
  }
}
// </vc-code>
