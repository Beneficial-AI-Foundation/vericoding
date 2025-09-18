// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TrapRainWater(height: array<nat>) returns (result: nat)
    requires height.Length >= 0
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    if height.Length <= 2 {
        result := 0;
        return;
    }
    
    var left := new nat[height.Length];
    var right := new nat[height.Length];
    
    left[0] := height[0];
    var i := 1;
    while i < height.Length
        invariant 1 <= i <= height.Length
        invariant forall k :: 0 <= k < i ==> left[k] >= 0
    {
        left[i] := if height[i] > left[i-1] then height[i] else left[i-1];
        i := i + 1;
    }
    
    right[height.Length-1] := height[height.Length-1];
    i := height.Length - 2;
    while i >= 0
        invariant -1 <= i < height.Length - 1
        invariant forall k :: i < k < height.Length ==> right[k] >= 0
    {
        right[i] := if height[i] > right[i+1] then height[i] else right[i+1];
        i := i - 1;
    }
    
    result := 0;
    i := 0;
    while i < height.Length
        invariant 0 <= i <= height.Length
        invariant result >= 0
    {
        var water_level := if left[i] < right[i] then left[i] else right[i];
        if water_level > height[i] {
            result := result + (water_level - height[i]);
        }
        i := i + 1;
    }
}
// </vc-code>
