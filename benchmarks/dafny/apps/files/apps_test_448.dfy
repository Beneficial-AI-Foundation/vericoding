Given n children numbered 1 to n, where child i needs at least a_i candies.
Children initially line up in order 1, 2, ..., n.
Distribution algorithm:
1. Give m candies to the first child in line
2. If the child has received enough candies (≥ a_i), they go home
3. Otherwise, the child goes to the end of the line
4. Repeat until all children go home
Find which child goes home last.

predicate ValidInput(n: int, m: int, a: seq<int>) {
    n > 0 && m > 0 && |a| == n && forall i :: 0 <= i < |a| ==> a[i] > 0
}

predicate ValidResult(result: int, n: int) {
    1 <= result <= n
}

function SumCandiesStillNeeded(queue: seq<seq<int>>): nat
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
{
    if |queue| == 0 then 0
    else
        var child := queue[0];
        var stillNeeded := if child[1] <= child[0] then 0 else child[1] - child[0];
        stillNeeded + SumCandiesStillNeeded(queue[1..])
}

lemma SumAppendLemma(queue: seq<seq<int>>, child: seq<int>)
    requires forall c :: c in queue ==> |c| == 3 && c[0] >= 0 && c[1] > 0
    requires |child| == 3 && child[0] >= 0 && child[1] > 0
    ensures SumCandiesStillNeeded(queue + [child]) == SumCandiesStillNeeded(queue) + (if child[1] <= child[0] then 0 else child[1] - child[0])
{
    if |queue| == 0 {
        assert queue + [child] == [child];
    } else {
        var head := queue[0];
        var tail := queue[1..];
        assert queue == [head] + tail;
        assert queue + [child] == [head] + tail + [child];
        assert queue + [child] == [head] + (tail + [child]);
        SumAppendLemma(tail, child);
    }
}

method solve(n: int, m: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, m, a)
    ensures ValidResult(result, n)
{
    var children: seq<seq<int>> := [];
    var i := 0;

    while i < |a|
        invariant 0 <= i <= |a|
        invariant |children| == i
        invariant forall j :: 0 <= j < |children| ==> |children[j]| == 3
        invariant forall j :: 0 <= j < |children| ==> children[j][0] >= 0
        invariant forall j :: 0 <= j < |children| ==> children[j][1] > 0
        invariant forall j :: 0 <= j < |children| ==> 1 <= children[j][2] <= n
    {
        children := children + [[0, a[i], i + 1]];
        i := i + 1;
    }

    while |children| > 1
        invariant |children| >= 1
        invariant forall j :: 0 <= j < |children| ==> |children[j]| == 3
        invariant forall j :: 0 <= j < |children| ==> children[j][0] >= 0
        invariant forall j :: 0 <= j < |children| ==> children[j][1] > 0
        invariant forall j :: 0 <= j < |children| ==> 1 <= children[j][2] <= n
        decreases |children|, SumCandiesStillNeeded(children)
    {
        var child := children[0];
        var oldSum := SumCandiesStillNeeded(children);
        var oldChildStillNeeded := if child[1] <= child[0] then 0 else child[1] - child[0];
        children := children[1..];
        var sumWithoutChild := SumCandiesStillNeeded(children);

        var candies_received := child[0] + m;
        var candies_needed := child[1];
        var child_number := child[2];

        if candies_needed > candies_received {
            var newChildStillNeeded := candies_needed - candies_received;
            assert newChildStillNeeded == oldChildStillNeeded - m;
            children := children + [[candies_received, candies_needed, child_number]];
            SumAppendLemma(children[..|children|-1], [candies_received, candies_needed, child_number]);
            assert SumCandiesStillNeeded(children) == sumWithoutChild + newChildStillNeeded;
            assert SumCandiesStillNeeded(children) == sumWithoutChild + oldChildStillNeeded - m;
            assert oldSum == sumWithoutChild + oldChildStillNeeded;
            assert SumCandiesStillNeeded(children) == oldSum - m;
            assert SumCandiesStillNeeded(children) < oldSum;
        }
    }

    result := children[0][2];
}
