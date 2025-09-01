

// <vc-helpers>
lemma IfAnyTripleThenIncreasingTriple(l: seq<int>)
    ensures exists i, j, k :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
        ==> exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0
{
    if exists i, j, k :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
    {
        var i, j, k :| 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0;
        if i < j && j < k
        {
            assert exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k]
// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l : seq<int>) returns (result : bool)
    // post-conditions-start
    ensures result ==> exists i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
    ensures !result ==> forall i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
lemma IfAnyTripleThenIncreasingTriple(l: seq<int>)
    ensures exists i, j, k :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
        ==> exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0
{
    if exists i, j, k :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
    {
        var i, j, k :| 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0;
        if i < j && j < k
        {
            assert exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k]
// </vc-code>

