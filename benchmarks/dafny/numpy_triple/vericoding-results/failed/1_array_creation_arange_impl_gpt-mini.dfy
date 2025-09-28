// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): StepPositiveIncreases - positive step increases sequence elements */
lemma StepPositiveIncreases(start: real, step: real, k: nat)
  requires step > 0.0
  ensures start + (k as real) * step < start + ((k + 1) as real) * step
  {
    assert ((k as real) * step) + step == ((k + 1) as real) * step;
    assert step > 0.0;
    assert start + (k as real) * step < start + ((k as real) * step + step);
    assert start + ((k as real) * step + step) == start + ((k + 1) as real) * step;
  }

/* helper modified by LLM (iteration 5): StepNegativeDecreases - negative step decreases sequence elements */
lemma StepNegativeDecreases(start: real, step: real, k: nat)
  requires step < 0.0
  ensures start + (k as real) * step > start + ((k + 1) as real) * step
  {
    assert ((k as real) * step) + step == ((k + 1) as real) * step;
    assert step < 0.0;
    assert start + (k as real) * step > start + ((k as real) * step + step);
    assert start + ((k as real) * step + step) == start + ((k + 1) as real) * step;
  }

/* helper modified by LLM (iteration 5): RatioPositiveDecreasesByOne - dividing positive gap by step decreases by exactly 1 */
lemma RatioPositiveDecreasesByOne(stop: real, cur: real, step: real)
  requires step > 0.0
  ensures ((stop - cur)/step) - ((stop - (cur + step))/step) == 1.0
  {
    assert ((stop - cur)/step) - ((stop - (cur + step))/step) == ((stop - cur) - (stop - (cur + step))) / step;
    assert (stop - cur) - (stop - (cur + step)) == -cur + (cur + step);
    assert -cur + (cur + step) == step;
    assert step / step == 1.0;
    assert ((stop - cur)/step) - ((stop - (cur + step))/step) == 1.0;
  }

/* helper modified by LLM (iteration 5): RatioNegativeDecreasesByOne - dividing negative gap by -step decreases by exactly 1 */
lemma RatioNegativeDecreasesByOne(stop: real, cur: real, step: real)
  requires step < 0.0
  ensures ((cur - stop)/(-step)) - (((cur + step) - stop)/(-step)) == 1.0
  {
    assert ((cur - stop)/(-step)) - (((cur + step) - stop)/(-step)) == ((cur - stop) - ((cur + step) - stop)) / (-step);
    assert (cur - stop) - ((cur + step) - stop) == -step;
    assert -step / (-step) == 1.0;
    assert ((cur - stop)/(-step)) - (((cur + step) - stop)/(-step)) == 1.0;
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
/* code modified by LLM (iteration 5): use simple positive/negative real gap as decreases and maintain cur==start+|s|*step invariant */
{
  var s: seq<real> := [];
  var cur := start;
  if step > 0.0 {
    while cur < stop
      invariant forall j :: 0 <= j < |s| ==> s[j] == start + (j as real) * step
      invariant cur == start + (|s| as real) * step
      invariant stop - cur > 0.0
      decreases stop - cur
    {
      s := s + [cur];
      cur := cur + step;
    }
  } else {
    while cur > stop
      invariant forall j :: 0 <= j < |s| ==> s[j] == start + (j as real) * step
      invariant cur == start + (|s| as real) * step
      invariant cur - stop > 0.0
      decreases cur - stop
    {
      s := s + [cur];
      cur := cur + step;
    }
  }
  result := s;
}
// </vc-code>
