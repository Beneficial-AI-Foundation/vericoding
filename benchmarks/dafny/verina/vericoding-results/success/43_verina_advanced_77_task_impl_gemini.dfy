// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: nat, b: nat): nat {
    if a < b then a else b
}

function max(a: nat, b: nat): nat {
    if a > b then a else b
}

/* helper modified by LLM (iteration 3): added helper method for calculating left maxes */
method ComputeLeftMaxes(height: array<nat>) returns (left_maxes: array<nat>)
    requires height.Length > 0
    ensures left_maxes.Length == height.Length
    ensures forall k :: 0 <= k < height.Length ==> left_maxes[k] >= height[k]
{
    var n := height.Length;
    left_maxes := new nat[n];
    left_maxes[0] := height[0];
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant left_maxes.Length == n
        invariant forall k :: 0 <= k < i ==> left_maxes[k] >= height[k]
    {
        left_maxes[i] := max(left_maxes[i-1], height[i]);
        i := i + 1;
    }
}

/* helper modified by LLM (iteration 3): added helper method for calculating right maxes */
method ComputeRightMaxes(height: array<nat>) returns (right_maxes: array<nat>)
    requires height.Length > 0
    ensures right_maxes.Length == height.Length
    ensures forall k :: 0 <= k < height.Length ==> right_maxes[k] >= height[k]
{
    var n := height.Length;
    right_maxes := new nat[n];
    right_maxes[n-1] := height[n-1];
    var j := n - 2;
    while j >= 0
        invariant -1 <= j <= n - 2
        invariant right_maxes.Length == n
        invariant forall k :: j < k < n ==> right_maxes[k] >= height[k]
    {
        right_maxes[j] := max(right_maxes[j+1], height[j]);
        j := j - 1;
    }
}
// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use helper methods to compute max arrays */
    var n := height.Length;
    if n < 3 {
        result := 0;
        return;
    }

    var left_maxes := ComputeLeftMaxes(height);
    var right_maxes := ComputeRightMaxes(height);

    result := 0;
    var k := 0;
    while k < n
        invariant 0 <= k <= n
        invariant result >= 0
        invariant forall i' :: 0 <= i' < n ==> left_maxes[i'] >= height[i']
        invariant forall i' :: 0 <= i' < n ==> right_maxes[i'] >= height[i']
    {
        var water_level := min(left_maxes[k], right_maxes[k]);
        result := result + (water_level - height[k]);
        k := k + 1;
    }
}
// </vc-code>
