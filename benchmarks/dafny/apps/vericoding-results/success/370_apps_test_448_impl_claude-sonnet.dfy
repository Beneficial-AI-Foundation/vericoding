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
lemma SumCandiesStillNeededNonnegative(queue: seq<seq<int>>)
    requires forall child :: child in queue ==> |child| == 3 && child[0] >= 0 && child[1] > 0
    ensures SumCandiesStillNeeded(queue) >= 0
{
    if |queue| == 0 {
    } else {
        SumCandiesStillNeededNonnegative(queue[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, m, a)
    ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
    var bestStart := 1;
    var bestSum := -1;
    var start := 1;
    
    while start <= n
        invariant 1 <= start <= n + 1
        invariant 1 <= bestStart <= n
        decreases n + 1 - start
    {
        var currentSum := 0;
        var candies := m;
        var i := 0;
        
        while i < n
            invariant 0 <= i <= n
            invariant candies >= 0
            invariant currentSum >= 0
            decreases n - i
        {
            var childIndex := ((start - 1) + i) % n;
            var needed := a[childIndex];
            var given := if candies >= needed then needed else candies;
            var stillNeeded := needed - given;
            currentSum := currentSum + stillNeeded;
            candies := candies - given;
            i := i + 1;
        }
        
        if bestSum == -1 || currentSum < bestSum {
            bestSum := currentSum;
            bestStart := start;
        }
        
        start := start + 1;
    }
    
    result := bestStart;
}
// </vc-code>

