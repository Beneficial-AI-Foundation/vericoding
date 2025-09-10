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
lemma SumCandiesStillNeededNonNegative(queue: seq<seq<int>>)
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
    ensures SumCandiesStillNeeded(queue) >= 0
{
}

lemma SumCandiesStillNeededTail(queue: seq<seq<int>>)
    requires |queue| > 0
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
    ensures SumCandiesStillNeeded(queue) == 
        (if queue[0][1] <= queue[0][0] then 0 else queue[0][1] - queue[0][0]) + 
        SumCandiesStillNeeded(queue[1..])
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, m, a)
    ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
    var queue := seq(|a|, i requires 0 <= i < |a| => [0, a[i], 0]);
    var index := 0;
    var m_local := m;
    
    while SumCandiesStillNeeded(queue) > 0
        invariant 0 <= index < |queue|
        invariant forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
        invariant m_local >= 0
        decreases SumCandiesStillNeeded(queue)
    {
        var current := queue[index];
        if m_local >= current[1] - current[0] {
            m_local := m_local - (current[1] - current[0]);
            queue := queue[index := [current[1], current[1], current[2] + 1]];
        } else {
            queue := queue[index := [current[0] + m_local, current[1], current[2] + 1]];
            m_local := 0;
        }
        index := (index + 1) % n;
    }
    
    result := 1;
    var maxRounds := -1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result >= 1
    {
        if queue[i][2] > maxRounds {
            maxRounds := queue[i][2];
            result := i + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

