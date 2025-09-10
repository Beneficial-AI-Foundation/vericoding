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

lemma SumCandiesStillNeededPreservesLength(queue: seq<seq<int>>, index: int, newChild: seq<int>)
    requires 0 <= index < |queue|
    requires |newChild| == 3 && newChild[0] >= 0 && newChild[1] > 0
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
    ensures forall child :: child in queue[index := newChild] ==> |child| == 3 && child[0] >= 0 && child[1] > 0
{
}

lemma ArrayBoundsInvariant(queue: seq<seq<int>>, n: int)
    requires forall child :: child in queue ==> |child| == 3
    requires |queue| == n
    ensures forall j :: 0 <= j < n ==> |queue[j]| == 3
{
}

lemma ValidChildIndex(queue: seq<seq<int>>, j: int)
    requires forall child :: child in queue ==> |child| == 3
    requires 0 <= j < |queue|
    ensures |queue[j]| == 3
{
}

lemma ValidChildIndexRemainsValid(queue: seq<seq<int>>, j: int, newChild: seq<int>)
    requires 0 <= j < |queue|
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
    requires |newChild| == 3 && newChild[0] >= 0 && newChild[1] > 0
    ensures forall child :: child in queue[j := newChild] ==> |child| == 3 && child[0] >= 0 && child[1] > 0
{
}

lemma SumCandiesDecreases(queue: seq<seq<int>>, m_local: int, index: int)
    requires |queue| > 0 && 0 <= index < |queue|
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
    requires m_local > 0
    requires SumCandiesStillNeeded(queue) > 0
    decreases SumCandiesStillNeeded(queue)
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, m, a)
    ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
    var queue := seq(|a|, i requires 0 <= i < |a| => [0, a[i], i]);
    var index := 0;
    var m_local := m;
    
    ArrayBoundsInvariant(queue, n);
    
    while SumCandiesStillNeeded(queue) > 0 && m_local > 0
        invariant 0 <= index < |queue|
        invariant |queue| == n
        invariant forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
        invariant m_local >= 0
        decreases SumCandiesStillNeeded(queue) + m_local
    {
        ValidChildIndex(queue, index);
        var current := queue[index];
        
        var needed := current[1] - current[0];
        if m_local >= needed && needed > 0 {
            m_local := m_local - needed;
            var newChild := [current[1], current[1], current[2]];
            ValidChildIndexRemainsValid(queue, index, newChild);
            queue := queue[index := newChild];
            SumCandiesDecreases(queue, m_local, index);
        } else if needed > 0 {
            var newChild := [current[0] + m_local, current[1], current[2]];
            ValidChildIndexRemainsValid(queue, index, newChild);
            queue := queue[index := newChild];
            m_local := 0;
            SumCandiesDecreases(queue, m_local, index);
        }
        index := (index + 1) % n;
    }
    
    result := 1;
    var maxRounds := -1;
    var i := 0;
    ArrayBoundsInvariant(queue, n);
    
    while i < n
        invariant 0 <= i <= n
        invariant result >= 1
        invariant forall j :: 0 <= j < n ==> 1 <= queue[j][2] + 1 <= n + 1
    {
        ValidChildIndex(queue, i);
        assert 0 <= queue[i][2] <= n - 1;
        if queue[i][2] > maxRounds {
            maxRounds := queue[i][2];
            result := queue[i][2] + 1;
        } else if queue[i][2] == maxRounds && result > queue[i][2] + 1 {
            result := queue[i][2] + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

