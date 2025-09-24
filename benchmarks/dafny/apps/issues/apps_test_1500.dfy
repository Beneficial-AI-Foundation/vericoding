// <vc-preamble>
predicate ValidInput(input1: seq<int>, input2: seq<int>)
{
    |input1| >= 2 && |input2| >= 2 &&
    input1[0] >= 2 && input1[0] <= 1000 &&
    input1[1] >= 1 && input1[1] <= 100000 &&
    |input2| == input1[0] &&
    (forall i :: 0 <= i < |input2| ==> 0 <= input2[i] <= 100000) &&
    (forall i :: 0 <= i < |input2| - 1 ==> input2[i] < input2[i+1])
}

predicate IsPossible(positions: seq<int>, k: int)
{
    forall i :: 1 <= i < |positions| ==> positions[i] - positions[i-1] <= k
}

function GreedyBikeCount(distances: seq<int>, k: int): int
    requires |distances| >= 1
    requires k >= 1
    requires forall i :: 0 <= i < |distances| ==> distances[i] > 0
    requires forall i :: 0 <= i < |distances| ==> distances[i] <= k
{
    GreedyBikeCountHelper(distances, k, 0, 1, 0)
}

function GreedyBikeCountHelper(distances: seq<int>, k: int, index: int, bikes: int, currentRange: int): int
    requires 0 <= index <= |distances|
    requires bikes >= 1
    requires k >= 1
    requires 0 <= currentRange <= k
    requires forall i :: 0 <= i < |distances| ==> distances[i] > 0
    requires forall i :: 0 <= i < |distances| ==> distances[i] <= k
    decreases |distances| - index
{
    if index == |distances| then
        bikes
    else
        var newRange := currentRange + distances[index];
        if newRange > k then
            GreedyBikeCountHelper(distances, k, index + 1, bikes + 1, distances[index])
        else
            GreedyBikeCountHelper(distances, k, index + 1, bikes, newRange)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input1: seq<int>, input2: seq<int>) returns (result: int)
    requires ValidInput(input1, input2)
    ensures result == -1 <==> !IsPossible(input2, input1[1])
    ensures result != -1 ==> result >= 1
    ensures result != -1 ==> (
        var distances := seq(|input2|-1, i requires 0 <= i < |input2|-1 => input2[i+1] - input2[i]);
        result == GreedyBikeCount(distances, input1[1])
    )
// </vc-spec>
// <vc-code>
{
    var n := input1[0];
    var k := input1[1];
    var x := input2;

    // Calculate distances between consecutive stations
    var distances: seq<int> := [];
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant |distances| == i - 1
        invariant forall j :: 0 <= j < |distances| ==> distances[j] == x[j+1] - x[j]
        invariant forall j :: 0 <= j < |distances| ==> distances[j] > 0
    {
        distances := distances + [x[i] - x[i-1]];
        i := i + 1;
    }

    // Prove that distances matches the spec distances
    var postDistances := seq(|input2|-1, i requires 0 <= i < |input2|-1 => input2[i+1] - input2[i]);
    assert |distances| == |postDistances|;
    assert forall j :: 0 <= j < |distances| ==> distances[j] == postDistances[j];
    assert distances == postDistances;

    // Check if any distance > k
    i := 0;
    var hasLargeDistance := false;
    while i < |distances|
        invariant 0 <= i <= |distances|
        invariant hasLargeDistance <==> (exists j :: 0 <= j < i && distances[j] > k)
    {
        if distances[i] > k {
            hasLargeDistance := true;
        }
        i := i + 1;
    }

    if hasLargeDistance {
        // Prove that !IsPossible(input2, input1[1])
        assert exists j :: 0 <= j < |distances| && distances[j] > k;
        var j :| 0 <= j < |distances| && distances[j] > k;
        assert distances[j] == x[j+1] - x[j];
        assert x[j+1] - x[j] > k;
        var m := j + 1;
        assert 1 <= m < |x| && x[m] - x[m-1] > k;
        assert !IsPossible(x, k);
        return -1;
    }

    // Prove that IsPossible(input2, input1[1])
    assert forall j :: 0 <= j < |distances| ==> distances[j] <= k;
    assert forall j :: 0 <= j < |distances| ==> x[j+1] - x[j] <= k;
    assert forall m :: 1 <= m < |x| ==> x[m] - x[m-1] <= k;
    assert IsPossible(x, k);

    // Simulate the journey using greedy approach
    var ans := 1;
    var r := 0;
    i := 0;
    while i < |distances|
        invariant 0 <= i <= |distances|
        invariant ans >= 1
        invariant 0 <= r <= k
        invariant forall j :: 0 <= j < |distances| ==> distances[j] <= k
        invariant GreedyBikeCountHelper(distances, k, 0, 1, 0) == GreedyBikeCountHelper(distances, k, i, ans, r)
    {
        var el := distances[i];
        var newRange := r + el;

        if newRange > k {
            ans := ans + 1;
            r := el;
        } else {
            r := newRange;
        }
        i := i + 1;
    }

    // Prove the postcondition
    assert GreedyBikeCountHelper(distances, k, 0, 1, 0) == GreedyBikeCountHelper(distances, k, |distances|, ans, r);
    assert GreedyBikeCountHelper(distances, k, |distances|, ans, r) == ans;
    assert GreedyBikeCount(distances, k) == ans;
    assert distances == postDistances;
    assert ans == GreedyBikeCount(postDistances, input1[1]);

    return ans;
}
// </vc-code>
