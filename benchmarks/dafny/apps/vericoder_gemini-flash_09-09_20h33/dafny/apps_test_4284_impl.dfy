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
            assert result == n; // result is n in this branch.
            assert 0 <= result <= n; // 0 <= n is true by ValidQuery and result == n
        } else {
            assert result == maxPossible; // result is maxPossible in this branch.
            // Need to show 0 <= maxPossible <= n
            // Since n <= maxPossible is false, maxPossible < n.
            // (k - n * b - 1) / (a - b) < n

            // To show maxPossible >= 0:
            // maxPossible is (k - n * b - 1) / (a - b).
            // We know a - b > 0 (from ValidQuery: a > b).
            // We are in the case where n * b <= k.
            // Also, result is not -1, which means result is either n or maxPossible, both non-negative.
            // If result == maxPossible, then maxPossible must be >= 0.
            // If k - n * b - 1 < 0, then maxPossible could be negative (e.g., -1 for (0-1)/(a-b)).
            // However, we entered this branch because result is not -1.
            // And within MaxActionATurns, result is -1 only if n*b > k.
            // But we are in the n*b <= k branch.
            // If (k - n * b - 1) / (a - b) evaluates to -1, it means k - n * b - 1 < 0 and -(a-b) <= k - n * b - 1 < 0.
            // For example, if k - n * b - 1 = -1, and a - b = 1, then maxPossible = -1.
            // This would only happen if k - n * b == 0, leading to (0 - 1)/(a - b), which might be -1.
            // But if k - n * b == 0, then maxPossible is (0 - 1)/(a - b) which is either 0 or -1.
            // It could be -1.  MaxActionATurns function will return maxPossible in this case, and if maxPossible is -1,
            // then current result is -1 which is invalid.
            // To prove result >=0, we consider two scenarios.
            // 1. maxPossible < 0: Then maxPossible = -1 (since it's an integer division).
            // If maxPossible = -1, then MaxActionATurns(..) returns -1.
            // But we are in "result != -1" branch. This proves that maxPossible >= 0.
            assert maxPossible >= 0;
            assert 0 <= result <= n; // result = maxPossible, maxPossible < n, and maxPossible >= 0.
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
    var newResults_array := new int[|queries|];
    for i := 0 to |queries| - 1
        invariant 0 <= i <= |queries|
        invariant forall j :: 0 <= j < i ==>
            var (k_j, n_j, a_j, b_j) := queries[j];
            newResults_array[j] == MaxActionATurns(k_j, n_j, a_j, b_j)
            && ValidResult(newResults_array[j], k_j, n_j, a_j, b_j)
    {
        var (k, n, a, b) := queries[i];

        var currentResult := MaxActionATurns(k, n, a, b);
        newResults_array[i] := currentResult;

        lemma_max_action_result_valid(k, n, a, b);
        assert ValidResult(newResults_array[i], k, n, a, b);
    }
    var results_seq: seq<int> := newResults_array[..];
    return results_seq;
}
// </vc-code>

