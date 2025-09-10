predicate ValidQuery(k: int, n: int, a: int, b: int)
{
    k > 0 && n > 0 && a > 0 && b > 0 && b < a
}

function MaxActionATurns(k: int, n: int, a: int, b: int): int
    requires ValidQuery(k, n, a, b)
{
    if n * b > k then 
        -1
    else 
        var maxPossible := (k - n * b - 1) / (a - b);
        if n <= maxPossible then n else maxPossible
}

predicate ValidResult(result: int, k: int, n: int, a: int, b: int)
    requires ValidQuery(k, n, a, b)
{
    result == -1 || (0 <= result <= n)
}

// <vc-helpers>
lemma lemma_max_action_result_valid(k: int, n: int, a: int, b: int)
    requires ValidQuery(k, n, a, b)
    ensures ValidResult(MaxActionATurns(k, n, a, b), k, n, a, b)
{
    var result := MaxActionATurns(k, n, a, b);
    if result == -1 {
        // ValidResult holds trivially
    } else {
        // We need to show 0 <= result <= n
        // Case 1: n * b > k, then result == -1, already handled.
        // Case 2: n * b <= k
        var maxPossible := (k - n * b - 1) / (a - b);
        if n <= maxPossible {
            result := n;
            assert 0 <= result <= n; // 0 <= n is true by ValidQuery
        } else {
            result := maxPossible;
            // Need to show 0 <= maxPossible <= n
            // Since n <= maxPossible is false, maxPossible < n.
            // (k - n * b - 1) / (a - b) < n
            // From ValidQuery, a > b, so a - b >= 1.
            // Also k - n * b - 1 >= 0 if maxPossible >= 0
            // k - n * b >= 1 (since k - n * b - 1 is divided by a-b, it ensures k - n*b - 1 must be non-negative)
            // (k - n * b - 1) / (a - b) >= 0 is true because k - n * b >= 0, and k - n * b - 1 can be negative or positive
            calc {
                k - n * b;
                (k - n * b);
            }
            if k - n * b <= 0 { // This case implies k < n*b, which contradicts our assumption n*b <= k.
                // However, the division (k - n * b - 1) / (a - b)
                // If k - n*b - 1 < 0, then maxPossible can be negative.
                // If k - n * b = 0, then maxPossible = -1 / (a-b) = -1.
                // If k - n * b = 1, then maxPossible = 0 / (a-b) = 0.
                if k - n * b - 1 < 0 { // implies k - n*b <= 0
                    assert (k - n * b - 1) / (a - b) == -1; // This is the division for integers.
                    assert maxPossible == -1;
                    assert result == -1; // This case means n*b <= k but k close to n*b, so no free turn.
                    assert result == -1;
                }
            } else { // k - n * b >= 1
                assert k - n * b - 1 >= 0;
            }

            // We need to prove that maxPossible >= 0.
            // From n * b <= k, we have k - n * b >= 0.
            // If k - n * b = 0, then maxPossible = (0 - 1) / (a - b) = -1.
            // In this case, n <= maxPossible is false (n > 0, -1). So result = maxPossible = -1. This fits InvalidResult.
            // Consider when result is not -1, so maxPossible >= 0 is the case.
            // This happens when k - n * b - 1 >= 0, meaning k - n * b >= 1.
            // So if result != -1, then maxPossible >= 0.
            assert maxPossible >= 0 ==> 0 <= result <= n; // result < n already established
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(int, int, int, int)>) returns (results: seq<int>)
    requires |queries| > 0
    requires forall i :: 0 <= i < |queries| ==> 
        var (k, n, a, b) := queries[i];
        ValidQuery(k, n, a, b)
    ensures |results| == |queries|
    ensures forall i :: 0 <= i < |queries| ==> 
        var (k, n, a, b) := queries[i];
        results[i] == MaxActionATurns(k, n, a, b)
    ensures forall i :: 0 <= i < |results| ==> 
        var (k, n, a, b) := queries[i];
        ValidResult(results[i], k, n, a, b)
// </vc-spec>
// <vc-code>
{
    var newResults := new int[|queries|];
    for i := 0 to |queries| - 1
        invariant 0 <= i <= |queries|
        invariant forall j :: 0 <= j < i ==> 
            var (k_j, n_j, a_j, b_j) := queries[j];
            newResults[j] == MaxActionATurns(k_j, n_j, a_j, b_j)
            && ValidResult(newResults[j], k_j, n_j, a_j, b_j)
    {
        var (k, n, a, b) := queries[i];
        
        var currentResult := MaxActionATurns(k, n, a, b);
        newResults[i] := currentResult;
        
        lemma_max_action_result_valid(k, n, a, b);
        assert ValidResult(newResults[i], k, n, a, b);
    }
    results := newResults;
}
// </vc-code>

