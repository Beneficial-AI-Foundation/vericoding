predicate ValidInput(n: int, v: int, sellers: seq<seq<int>>) {
    n >= 0 && v >= 0 && |sellers| == n && 
    forall i :: 0 <= i < |sellers| ==> |sellers[i]| > 0
}

predicate ValidOutput(count: int, indices: seq<int>, n: int) {
    count == |indices| && count >= 0 && count <= n &&
    (forall i :: 0 <= i < |indices| ==> 1 <= indices[i] <= n) &&
    (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i+1])
}

predicate CorrectSolution(v: int, sellers: seq<seq<int>>, indices: seq<int>) 
    requires forall i :: 0 <= i < |sellers| ==> |sellers[i]| > 0
    requires forall i :: 0 <= i < |indices| ==> 1 <= indices[i] <= |sellers|
{
    (forall i :: 0 <= i < |indices| ==> v > Min(sellers[indices[i] - 1])) &&
    (forall i :: 0 <= i < |sellers| ==> (v > Min(sellers[i]) <==> (i + 1) in indices))
}

// <vc-helpers>
function Min(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0] else min(s[0], Min(s[1..]))
}

predicate In<T>(t: T, s: seq<T>) {
    exists i :: 0 <= i < |s| && s[i] == t
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, v: int, sellers: seq<seq<int>>) returns (count: int, indices: seq<int>)
    requires ValidInput(n, v, sellers)
    ensures ValidOutput(count, indices, n)
    ensures CorrectSolution(v, sellers, indices)
// </vc-spec>
// <vc-code>
{
    var resultIndices: seq<int> := [];
    var resultCount: int := 0;

    // Iterate through each seller to identify those whose minimum value is less than v
    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant ValidOutput(resultCount, resultIndices, i) // resultIndices contains indices from 1 to i
        invariant forall k :: 0 <= k < i && (v > Min(sellers[k]) <==> In(k + 1, resultIndices))
        invariant forall k :: 0 <= k < resultCount ==> v > Min(sellers[resultIndices[k] - 1])
    {
        if v > Min(sellers[i]) {
            resultIndices := resultIndices + [i + 1];
            resultCount := resultCount + 1;
        }
    }

    // Ensure the output indices are sorted
    // The current construction guarantees sorted indices because i+1 is always increasing.
    // We already maintain resultIndices sorted in the loop.

    count := resultCount;
    indices := resultIndices;
}
// </vc-code>

