predicate ValidInput(n: int, k: int, requests: seq<int>)
{
    n >= 1 && k >= 1 && |requests| == n &&
    forall i :: 0 <= i < |requests| ==> 1 <= requests[i] <= n
}

predicate ValidSolution(n: int, k: int, requests: seq<int>, cost: int)
{
    ValidInput(n, k, requests) && cost >= 0 && cost <= n
}

// <vc-helpers>
function method CountUnique(requests: seq<int>): int
{
    |set i | 0 <= i < |requests| :: requests[i]|
}

lemma CountUniqueBound(requests: seq<int>, n: int)
    requires |requests| == n
    requires forall i :: 0 <= i < |requests| ==> 1 <= requests[i] <= n
    ensures 0 <= CountUnique(requests) <= n
{
    var uniqueSet := set i | 0 <= i < |requests| :: requests[i];
    assert forall x :: x in uniqueSet ==> 1 <= x <= n;
    assert |uniqueSet| <= n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, requests: seq<int>) returns (cost: int)
    requires ValidInput(n, k, requests)
    ensures ValidSolution(n, k, requests, cost)
// </vc-spec>
// <vc-code>
{
    var uniqueCount := CountUnique(requests);
    cost := if uniqueCount <= k then uniqueCount else k;
    
    // Prove the postcondition
    CountUniqueBound(requests, n);
    assert 0 <= uniqueCount <= n;
    assert cost <= uniqueCount;
    assert cost <= n;
}
// </vc-code>

