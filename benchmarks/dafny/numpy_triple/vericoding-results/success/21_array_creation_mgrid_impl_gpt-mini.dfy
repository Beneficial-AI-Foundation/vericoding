// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): cast floor to real when comparing */
lemma floor_le(x: real, k: int)
  requires k == x.Floor
  ensures (k as real) <= x
{
  assert (k as real) <= x;
}

/* helper modified by LLM (iteration 3): show index times step less than stop */
lemma grid_index_lt_stop(start: real, stop: real, step: real, n: int, i: int)
  requires step > 0.0
  requires start < stop
  requires n == ((stop - start) / step).Floor
  requires 0 <= i < n
  ensures start + (i as real) * step < stop
{
  var x := (stop - start) / step;
  floor_le(x, n);
  assert (n as real) <= x;
  assert (i as real) < (n as real);
  assert (i as real) < x;
  assert (i as real) * step < x * step;
  assert start + (i as real) * step < start + x * step;
  assert start + x * step == stop;
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
/* code modified by LLM (iteration 3): implement mgrid using loop and helper */
{
  var n := ((stop - start) / step).Floor;
  assert n >= 0;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == start + (j as real) * step
    decreases n - i
  {
    var val := start + (i as real) * step;
    grid_index_lt_stop(start, stop, step, n, i);
    result := result + [val];
    i := i + 1;
  }
}

// </vc-code>
