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
            assert 0 <= result <= n; // 0 <= n is true by ValidQuery and result == n
        } else {
            result := maxPossible;
            // Need to show 0 <= maxPossible <= n
            // Since n <= maxPossible is false, maxPossible < n.
            // (k - n * b - 1) / (a - b) < n

            // To show maxPossible >= 0:
            // maxPossible is (k - n * b - 1) / (a - b).
            // Since a - b > 0 (from ValidQuery: a > b), we need k - n * b - 1 >= 0 for maxPossible to be non-negative.
            // If k - n * b - 1 < 0, then maxPossible must be negative (integer division rounds towards zero, so (-X) / Y = -(X/Y)).
            // Specifically, if k - n * b - 1 < 0, it means k - n * b <= 0.
            // But we are in the case where n * b <= k, so k - n * b >= 0.
            // These two imply k - n * b = 0.
            // If k - n * b = 0, then maxPossible = (0 - 1) / (a - b) = -1.
            // In this specific subcase where maxPossible = -1:
            // Since we established that `result` is not -1, this subcase where `maxPossible` is -1 can't be the current branch.
            // So, it must be that `maxPossible >= 0`.
            // This means k - n * b - 1 >= 0, thus k - n * b >= 1.
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
        assert ValidResult(newResults[i] as int, k, n, a, b);
    }
    results := newResults as seq<int>;
}
// </vc-code>

