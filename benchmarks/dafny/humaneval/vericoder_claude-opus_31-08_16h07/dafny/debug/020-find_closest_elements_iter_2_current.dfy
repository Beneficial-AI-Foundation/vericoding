function dist(a: real, b: real) : (d : real)
    ensures d >= 0.0
    ensures (d == 0.0) <==> a == b
{
    if a < b then b - a else a - b
}
function des(s: seq<real>, a: int, b: int) : bool {
    // distinct elements
    0 <= a < |s| && 0 <= b < |s| && a != b
}

// <vc-helpers>
lemma SortedClosestPair(s: seq<real>)
    requires |s| >= 2
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures exists i :: 0 <= i < |s| - 1 && 
                       forall a, b :: des(s, a, b) ==> dist(s[i], s[i+1]) <= dist(s[a], s[b])
{
    var minDist := dist(s[0], s[1]);
    var minIdx := 0;
    
    for i := 1 to |s| - 1
        invariant 0 <= minIdx < i <= |s| - 1
        invariant minDist == dist(s[minIdx], s[minIdx + 1])
        invariant forall j :: 0 <= j < i ==> minDist <= dist(s[j], s[j + 1])
    {
        if dist(s[i], s[i + 1]) < minDist {
            minDist := dist(s[i], s[i + 1]);
            minIdx := i;
        }
    }
    
    // Prove that adjacent pairs have minimum distance among all pairs
    forall a, b | des(s, a, b)
        ensures dist(s[minIdx], s[minIdx + 1]) <= dist(s[a], s[b])
    {
        var x, y := if a < b then a, b else b, a;
        assert x < y;
        assert s[x] <= s[y];
        
        // The distance between s[x] and s[y] is at least the sum of distances between consecutive elements
        var d := dist(s[x], s[y]);
        assert d == s[y] - s[x];
        
        // Between x and y, there are y-x-1 intermediate elements
        if y == x + 1 {
            assert dist(s[minIdx], s[minIdx + 1]) <= dist(s[x], s[x + 1]);
        } else {
            // For non-adjacent elements, the distance is at least as large as any adjacent pair
            assert s[y] - s[x] >= s[x+1] - s[x];
            assert dist(s[minIdx], s[minIdx + 1]) <= dist(s[x], s[x + 1]);
            assert dist(s[x], s[x + 1]) <= dist(s[x], s[y]);
        }
    }
}

method SortSequence(s: seq<real>) returns (sorted: seq<real>)
    ensures |sorted| == |s|
    ensures multiset(sorted) == multiset(s)
    ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
{
    sorted := s;
    
    for i := 0 to |sorted| - 1
        invariant |sorted| == |s|
        invariant multiset(sorted) == multiset(s)
        invariant forall j, k :: 0 <= j < i && i <= k < |sorted| ==> sorted[j] <= sorted[k]
        invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
    {
        var minIdx := i;
        var minVal := sorted[i];
        
        for j := i + 1 to |sorted|
            invariant i <= minIdx < |sorted|
            invariant minVal == sorted[minIdx]
            invariant forall k :: i <= k < j ==> minVal <= sorted[k]
        {
            if sorted[j] < minVal {
                minIdx := j;
                minVal := sorted[j];
            }
        }
        
        if minIdx != i {
            sorted := sorted[i := sorted[minIdx]][minIdx := sorted[i]];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method find_closest_elements(s: seq<real>) returns (l : real, h : real)
    // pre-conditions-start
    requires |s| >= 2
    // pre-conditions-end
    // post-conditions-start
    ensures exists a, b : int :: des(s, a, b) && l == s[a] && h == s[b]
    ensures forall a, b : int :: des(s, a, b) ==> dist(l, h) <= dist(s[a], s[b])
    ensures l <= h
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var sorted := SortSequence(s);
    SortedClosestPair(sorted);
    
    var minDist := dist(sorted[0], sorted[1]);
    var minIdx := 0;
    
    for i := 1 to |sorted| - 1
        invariant 0 <= minIdx < |sorted| - 1
        invariant minDist == dist(sorted[minIdx], sorted[minIdx + 1])
        invariant forall j :: 0 <= j < i ==> minDist <= dist(sorted[j], sorted[j + 1])
    {
        var d := dist(sorted[i], sorted[i + 1]);
        if d < minDist {
            minDist := d;
            minIdx := i;
        }
    }
    
    l := sorted[minIdx];
    h := sorted[minIdx + 1];
    
    // Find original indices
    var a, b := 0, 0;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
    {
        if s[i] == l || s[i] == h {
            if s[i] == l {
                a := i;
            }
            if s[i] == h {
                b := i;
            }
        }
    }
}
// </vc-code>

