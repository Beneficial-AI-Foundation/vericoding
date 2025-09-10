predicate ValidInput(n: int, k: int, L: seq<int>)
{
    n >= 1 && k >= 1 && n <= 2*k &&
    |L| == n &&
    (forall i :: 0 <= i < |L|-1 ==> L[i] <= L[i+1]) &&
    (forall i :: 0 <= i < |L| ==> L[i] >= 0)
}

predicate ValidBoxConfiguration(boxes: seq<int>, boxSize: int)
{
    |boxes| >= 1 &&
    (forall i :: 0 <= i < |boxes| ==> boxes[i] <= boxSize) &&
    (forall i :: 0 <= i < |boxes| ==> boxes[i] >= 0)
}

function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function max(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= max(s[1..]) then s[0]
    else max(s[1..])
}

// <vc-helpers>
lemma SumEmpty()
    ensures sum([]) == 0
{
}

lemma SumSingleton(x: int)
    ensures sum([x]) == x
{
}

lemma MaxProperties(s: seq<int>)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= max(s)
    ensures exists i :: 0 <= i < |s| && s[i] == max(s)
{
    if |s| == 1 {
        // Base case: the only element is the max
        assert s[0] == max(s);
        assert 0 <= 0 < |s| && s[0] == max(s);
    } else {
        MaxProperties(s[1..]);
        // Either s[0] is the max or something in s[1..] is
        if s[0] >= max(s[1..]) {
            assert max(s) == s[0];
            assert 0 <= 0 < |s| && s[0] == max(s);
        } else {
            assert max(s) == max(s[1..]);
            var j :| 0 <= j < |s[1..]| && s[1..][j] == max(s[1..]);
            assert s[1+j] == max(s);
            assert 0 <= 1+j < |s| && s[1+j] == max(s);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
    requires ValidInput(n, k, L)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    if k >= n {
        // Each item can go in its own box
        assert n >= 1;
        assert |L| == n;
        assert |L| >= 1;
        MaxProperties(L);
        result := max(L);
    } else {
        // Need to distribute n items into k boxes
        // Simple greedy approach: put items in order into boxes
        var boxes := seq(k, i => 0);
        var i := 0;
        
        while i < n
            invariant 0 <= i <= n
            invariant |boxes| == k
            invariant forall j :: 0 <= j < |boxes| ==> boxes[j] >= 0
        {
            // Find box with minimum current load
            var minIdx := 0;
            var j := 1;
            while j < k
                invariant 0 <= j <= k
                invariant 0 <= minIdx < k
                invariant forall m :: 0 <= m < j ==> boxes[minIdx] <= boxes[m]
            {
                if boxes[j] < boxes[minIdx] {
                    minIdx := j;
                }
                j := j + 1;
            }
            
            // Add current item to the box with minimum load
            boxes := boxes[minIdx := boxes[minIdx] + L[i]];
            i := i + 1;
        }
        
        assert |boxes| == k;
        assert k >= 1;
        assert |boxes| >= 1;
        MaxProperties(boxes);
        result := max(boxes);
    }
}
// </vc-code>

