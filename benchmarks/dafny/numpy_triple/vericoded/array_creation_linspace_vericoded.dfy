// <vc-preamble>
// Helper function to compute minimum of two reals
function min(a: real, b: real): real
{
    if a <= b then a else b
}

// Helper function to compute maximum of two reals  
function max(a: real, b: real): real
{
    if a >= b then a else b
}

// Helper function to compute absolute value
function abs(x: real): real
{
    if x >= 0.0 then x else -x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove monotonicity properties */
lemma LinspaceMonotonicity(num: nat, start: real, stop: real, step: real, result: seq<real>)
  requires num > 1
  requires step == (stop - start) / ((num - 1) as real)
  requires |result| == num
  requires forall i | 0 <= i < num :: result[i] == start + (i as real) * step
  ensures start < stop ==> forall i, j | 0 <= i < j < num :: result[i] < result[j]
  ensures start > stop ==> forall i, j | 0 <= i < j < num :: result[i] > result[j]
  ensures start == stop ==> forall i | 0 <= i < num :: result[i] == start
{
  if start < stop {
    forall i, j | 0 <= i < j < num
      ensures result[i] < result[j]
    {
      assert result[i] == start + (i as real) * step;
      assert result[j] == start + (j as real) * step;
      assert step > 0.0;
      assert (j - i) > 0;
      assert result[j] - result[i] == ((j - i) as real) * step;
      assert result[j] - result[i] > 0.0;
    }
  } else if start > stop {
    forall i, j | 0 <= i < j < num
      ensures result[i] > result[j]
    {
      assert result[i] == start + (i as real) * step;
      assert result[j] == start + (j as real) * step;
      assert step < 0.0;
      assert (j - i) > 0;
      assert result[j] - result[i] == ((j - i) as real) * step;
      assert result[j] - result[i] < 0.0;
    }
  } else {
    forall i | 0 <= i < num
      ensures result[i] == start
    {
      assert step == 0.0;
      assert result[i] == start + (i as real) * 0.0;
      assert result[i] == start;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method linspace(num: nat, start: real, stop: real) returns (result: seq<real>)
    requires num > 0
    ensures |result| == num
    
    // First element is always start
    ensures result[0] == start
    
    // Special case: when num = 1, the single element is start
    ensures num == 1 ==> forall i | 0 <= i < |result| :: result[i] == start
    
    // General case: when num > 1
    ensures num > 1 ==> 
        var step := (stop - start) / (num - 1) as real;
        // Last element is stop
        result[num - 1] == stop &&
        // All elements follow the linear formula
        (forall i | 0 <= i < num :: result[i] == start + (i as real) * step) &&
        // Consecutive elements have constant spacing
        (forall i | 0 <= i < num - 1 :: result[i + 1] - result[i] == step)
    
    // Monotonicity properties
    ensures start < stop ==> forall i, j | 0 <= i < j < num :: result[i] < result[j]
    ensures start > stop ==> forall i, j | 0 <= i < j < num :: result[i] > result[j]
    ensures start == stop ==> forall i | 0 <= i < num :: result[i] == start
    
    // Bounds property: all elements lie within the interval
    ensures forall i | 0 <= i < num :: 
        result[i] >= min(start, stop) && result[i] <= max(start, stop)
    
    // Linear interpolation property: each element can be expressed as a weighted average
    ensures num > 1 ==> forall i | 0 <= i < num ::
        var t := (i as real) / ((num - 1) as real);
        result[i] == (1.0 - t) * start + t * stop
    
    // Reverse symmetry property with guards matching Lean specification
    ensures num > 1 ==> forall i | 0 <= i < num - 1 ::
        var j := num - 1 - i;
        0 <= j < num && result[i] == stop + (j as real) * ((start - stop) / ((num - 1) as real))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added assertions to help verify monotonicity */
  if num == 1 {
    result := [start];
  } else {
    var step := (stop - start) / ((num - 1) as real);
    result := [];
    var i := 0;
    while i < num
      invariant 0 <= i <= num
      invariant |result| == i
      invariant forall k | 0 <= k < i :: result[k] == start + (k as real) * step
      invariant i > 0 ==> forall k | 0 <= k < i - 1 :: result[k + 1] - result[k] == step
    {
      result := result + [start + (i as real) * step];
      i := i + 1;
    }
    
    // Call helper lemma to establish monotonicity properties
    LinspaceMonotonicity(num, start, stop, step, result);
    
    // Assert final element is stop
    assert result[num - 1] == start + ((num - 1) as real) * step;
    assert result[num - 1] == start + ((num - 1) as real) * ((stop - start) / ((num - 1) as real));
    assert result[num - 1] == stop;
    
    // Help verifier with reverse symmetry property
    forall i | 0 <= i < num - 1
      ensures var j := num - 1 - i; 0 <= j < num && result[i] == stop + (j as real) * ((start - stop) / ((num - 1) as real))
    {
      var j := num - 1 - i;
      assert 0 <= j < num;
      assert result[i] == start + (i as real) * step;
      assert step == (stop - start) / ((num - 1) as real);
      assert result[i] == start + (i as real) * ((stop - start) / ((num - 1) as real));
      assert result[i] == stop + (j as real) * ((start - stop) / ((num - 1) as real));
    }
  }
}
// </vc-code>
