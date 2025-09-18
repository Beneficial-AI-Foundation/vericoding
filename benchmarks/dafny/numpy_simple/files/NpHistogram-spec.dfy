// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
{
    assume {:axiom} false;
}
// </vc-code>
