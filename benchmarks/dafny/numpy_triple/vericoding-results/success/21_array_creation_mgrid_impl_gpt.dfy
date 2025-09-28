// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added explicit triggers to silence warnings and preserve proof that generated points are < stop */
lemma BoundsLessThanStopForIndex(start: real, stop: real, step: real)
  requires step > 0.0
  requires start < stop
  ensures forall i {:trigger start + (i as real) * step} ::
            0 <= i < (((stop - start) / step).Floor) ==> start + (i as real) * step < stop
{
  var x := (stop - start) / step;
  var n := x.Floor;
  forall i {:trigger start + (i as real) * step} | 0 <= i < n
    ensures start + (i as real) * step < stop
  {
    assert (i as real) < (n as real);
    assert step > 0.0;
    assert (i as real) * step < (n as real) * step;
    assert start + (i as real) * step < start + (n as real) * step;
    assert (n as real) <= x;
    assert (n as real) * step <= x * step;
    assert start + (n as real) * step <= start + x * step;
    assert start + x * step == stop;
  }
}
// </vc-helpers>

// <vc-spec>
method mgrid(start: real, stop: real, step: real) returns (result: seq<real>)
  // Input constraints
  requires step > 0.0
  requires start < stop
  requires ((stop - start) / step).Floor >= 0  // Ensure non-negative sequence length
  
  // Output constraints  
  ensures var n := ((stop - start) / step).Floor;
          n >= 0 && |result| == n
  ensures forall i :: 0 <= i < |result| ==>
    result[i] == start + (i as real) * step
  ensures forall i :: 0 <= i < |result| ==>
    result[i] < stop
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Build sequence iteratively and apply lemma for < stop bound */
  var n := ((stop - start) / step).Floor;
  var res: seq<real> := [];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall j :: 0 <= j < |res| ==> res[j] == start + (j as real) * step
    decreases n - i
  {
    res := res + [start + (i as real) * step];
    i := i + 1;
  }
  result := res;
  BoundsLessThanStopForIndex(start, stop, step);
}
// </vc-code>
