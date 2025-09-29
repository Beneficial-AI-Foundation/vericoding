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

// <vc-helpers>
lemma SumCandiesStillNeededMonotonic(queue: seq<seq<int>>, additionalCandies: nat)
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
    requires |queue| > 0
    requires queue[0][0] + additionalCandies <= queue[0][1]
    ensures SumCandiesStillNeeded([[queue[0][0] + additionalCandies, queue[0][1], queue[0][2]]] + queue[1..]) <= SumCandiesStillNeeded(queue) - additionalCandies
{
    var updatedChild := [queue[0][0] + additionalCandies, queue[0][1], queue[0][2]];
    var updatedQueue := [updatedChild] + queue[1..];
    
    var originalStillNeeded := if queue[0][1] <= queue[0][0] then 0 else queue[0][1] - queue[0][0];
    var updatedStillNeeded := if updatedChild[1] <= updatedChild[0] then 0 else updatedChild[1] - updatedChild[0];
    
    assert updatedStillNeeded == if originalStillNeeded >= additionalCandies then originalStillNeeded - additionalCandies else 0;
    assert SumCandiesStillNeeded(updatedQueue) == updatedStillNeeded + SumCandiesStillNeeded(queue[1..]);
    assert SumCandiesStillNeeded(queue) == originalStillNeeded + SumCandiesStillNeeded(queue[1..]);
}

function SumSeq(s: seq<int>): nat
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
{
    if |s| == 0 then 0
    else s[0] + SumSeq(s[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, m, a)
    ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
    var queue := seq(n, i requires 0 <= i < n => [0, a[i], i + 1]);
    var remainingCandies := m;
    var currentIndex := 0;
    
    while currentIndex < n && remainingCandies > 0
        invariant 0 <= currentIndex <= n
        invariant 0 <= remainingCandies <= m
        invariant |queue| == n
        invariant forall i :: 0 <= i < n ==> |queue[i]| == 3 && queue[i][1] == a[i] && queue[i][2] == i + 1
        invariant forall i :: 0 <= i < n ==> 0 <= queue[i][0] <= queue[i][1]
        invariant forall i :: 0 <= i < currentIndex ==> queue[i][0] == queue[i][1]
        invariant forall i :: currentIndex < i < n ==> queue[i][0] == 0
        invariant currentIndex < n ==> queue[currentIndex][0] <= queue[currentIndex][1]
    {
        var child := queue[currentIndex];
        var needed := child[1] - child[0];
        
        if remainingCandies >= needed {
            queue := queue[currentIndex := [child[1], child[1], child[2]]];
            remainingCandies := remainingCandies - needed;
            currentIndex := currentIndex + 1;
        } else {
            queue := queue[currentIndex := [child[0] + remainingCandies, child[1], child[2]]];
            remainingCandies := 0;
        }
    }
    
    if currentIndex == n && remainingCandies > 0 {
        var round := 0;
        while round < n && remainingCandies > 0
            invariant 0 <= round <= n
            invariant 0 <= remainingCandies
            invariant |queue| == n
            invariant forall i :: 0 <= i < n ==> |queue[i]| == 3 && queue[i][1] == a[i] && queue[i][2] == i + 1
            invariant forall i :: 0 <= i < n ==> 0 <= queue[i][0]
        {
            var child := queue[round];
            queue := queue[round := [child[0] + 1, child[1], child[2]]];
            remainingCandies := remainingCandies - 1;
            round := round + 1;
        }
    }
    
    var upset := 1;
    var i := n - 1;
    while i >= 0
        invariant -1 <= i < n
        invariant 1 <= upset <= n
        invariant forall j :: i < j < n && queue[j][0] < queue[j][1] ==> upset <= j + 1
    {
        if queue[i][0] < queue[i][1] {
            upset := i + 1;
        }
        i := i - 1;
    }
    
    result := upset;
}
// </vc-code>

