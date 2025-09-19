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
  assume {:axiom} false;
}
// </vc-code>
