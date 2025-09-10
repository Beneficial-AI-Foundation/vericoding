predicate ValidQuery(query: (int, int))
{
    query.0 >= 1 && query.0 <= query.1
}

predicate ValidInput(queries: seq<(int, int)>)
{
    forall i :: 0 <= i < |queries| ==> ValidQuery(queries[i])
}

function ArrayElement(i: int): int
    requires i >= 1
{
    i * (if i % 2 == 1 then -1 else 1)
}

function RangeSum(l: int, r: int): int
    requires l >= 1
    decreases r - l + 1
{
    if l > r then 0 else ArrayElement(l) + RangeSum(l + 1, r)
}

function PrefixSum(k: int): int
{
    if k % 2 == 0 then k / 2 else -(k + 1) / 2
}

predicate CorrectResult(queries: seq<(int, int)>, results: seq<int>)
    requires ValidInput(queries)
{
    |results| == |queries| &&
    forall i :: 0 <= i < |queries| ==> results[i] == PrefixSum(queries[i].1) - PrefixSum(queries[i].0 - 1)
}

// <vc-helpers>
function CalcPrefixSum(k: int): int
    reads {}
    ensures CalcPrefixSum(k) == PrefixSum(k)
{
    if k == 0 then 0
    else if k % 2 == 0 then k / 2
    else -(k + 1) / 2
}

// Add a lemma to prove the equivalence of PrefixSum and CalcPrefixSum
lemma PrefixSumEquivalence(k: int)
    ensures PrefixSum(k) == CalcPrefixSum(k)
{
    // The proof simply follows from the definitions of PrefixSum and CalcPrefixSum
    // which are identical for k != 0. For k = 0, PrefixSum is not defined,
    // but CalcPrefixSum is. The problem statement implies k >= 1 when PrefixSum is used
    // in the context of queries.
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(int, int)>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures CorrectResult(queries, results)
// </vc-spec>
// <vc-code>
{
    var results_arr := new int[|queries|];
    for i := 0 to |queries| - 1
        invariant 0 <= i <= |queries|
        invariant forall j :: 0 <= j < i ==> results_arr[j] == PrefixSum(queries[j].1) - PrefixSum(queries[j].0 - 1)
    {
        var query := queries[i];
        results_arr[i] := CalcPrefixSum(query.1) - CalcPrefixSum(query.0 - 1);
        // We know CalcPrefixSum(k) == PrefixSum(k) by definition
        // For the loop invariant, we need to ensure that the result stored is indeed
        // PrefixSum(query.1) - PrefixSum(query.0 - 1).
        // The lemma PrefixSumEquivalence can be used here if explicity needed by the verifier,
        // but given the definitions are identical for k > 0, it might be inferred.
    }
    return results_arr[..];
}
// </vc-code>

