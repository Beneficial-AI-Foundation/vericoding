// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
function max(a: int, b: int): int { if a > b then a else b }
/* helper modified by LLM (iteration 2): changed function to method to allow loop */
method find_bin_index(value: real, bins: array<real>) returns (idx: int)
    requires bins.Length >= 2
    ensures 0 <= idx < bins.Length - 1
{
    var i := 0;
    while i < bins.Length - 1
        invariant 0 <= i <= bins.Length - 1
    {
        if bins[i] <= value < bins[i+1] {
            idx := i;
            return;
        }
        i := i + 1;
    }
    idx := bins.Length - 2;
}
// </vc-helpers>

// <vc-spec>
method histogram(data: array<real>, bins: array<real>) returns (result: array<int>)
    requires 
        bins.Length >= 2
    ensures
        result.Length == bins.Length - 1
{
    assume {:axiom} false;
}

method histogram_helper(data: array<real>, bins: array<real>, hist: array<int>, index: int) returns (result: array<int>)
    requires 
        bins.Length >= 2 &&
        hist.Length == bins.Length - 1
    ensures
        result.Length == bins.Length - 1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implemented histogram functionality */
{
    result := new int[bins.Length - 1];
    var i := 0;
    while i < data.Length
        invariant 0 <= i <= data.Length
        invariant result.Length == bins.Length - 1
    {
        var binIndex := find_bin_index(data[i], bins);
        result[binIndex] := result[binIndex] + 1;
        i := i + 1;
    }
}
// </vc-code>
