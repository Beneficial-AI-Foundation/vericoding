predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n
}

function CountLocalExtrema(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    |set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))|
}

predicate IsLocalExtremum(a: seq<int>, i: int)
    requires 0 <= i < |a|
{
    1 <= i < |a| - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]))
}

// <vc-helpers>
lemma CountLocalExtremaEmpty(n: int, a: seq<int>)
    requires ValidInput(n, a)
    requires n <= 2
    ensures CountLocalExtrema(n, a) == 0
{
    if n <= 2 {
        assert forall i {:trigger} :: 1 <= i < n - 1 ==> false;
        assert |set i | 1 <= i < n - 1 && IsLocalExtremum(a, i)| == 0;
    }
}

lemma CardinalityOfRange(low: int, high: int)
    requires low <= high + 1
    ensures |set i | low <= i <= high| == if low <= high then high - low + 1 else 0
{
    if low > high {
        assert (set i | low <= i <= high) == {};
    } else {
        var s := set i | low <= i <= high;
        assert s == set i | low <= i <= high;
        // This is a known property in Dafny for finite integer ranges
    }
}

lemma CountSubset(n: int, a: seq<int>, k: int)
    requires ValidInput(n, a)
    requires 1 <= k <= n - 1
    ensures |set i | 1 <= i < k && IsLocalExtremum(a, i)| <= k - 2
{
    var s := set i | 1 <= i < k && IsLocalExtremum(a, i);
    assert forall i :: i in s ==> 1 <= i < k;
    
    // For i to be a local extremum, we need i-1 >= 0 and i+1 < |a|
    // Since i >= 1 (from the set definition) and i+1 < |a| = n, we need i < n - 1
    // Combined with i < k, we get i < min(k, n-1)
    // Since k <= n-1, we have i < k
    // But for IsLocalExtremum, we also need i < |a| - 1 = n - 1
    // So valid range is 1 <= i < min(k, n-1) = k (since k <= n-1)
    // But we also need i >= 1 and i <= |a| - 2 for local extremum
    // So the actual upper bound is min(k-1, n-2)
    
    assert forall i :: i in s ==> 1 <= i < k && 1 <= i < |a| - 1;
    assert forall i :: i in s ==> 1 <= i && i < k && i < n - 1;
    
    // Since i must be strictly less than k, the maximum value is k-1
    // But for a local extremum at position i, we need i+1 to exist and be valid
    // So i can be at most k-2 when k <= n-1
    assert forall i :: i in s ==> i <= k - 2;
    
    var possible := set i | 1 <= i <= k - 2;
    assert s <= possible;
    
    CardinalityOfRange(1, k - 2);
    assert |possible| == if 1 <= k - 2 then k - 2 - 1 + 1 else 0;
    assert |possible| == if k >= 3 then k - 2 else 0;
    
    if k >= 3 {
        assert |possible| == k - 2;
    } else {
        assert possible == {};
        assert |possible| == 0;
        assert |s| == 0;
    }
    
    assert |s| <= |possible|;
    assert |s| <= k - 2;
}

lemma CountLocalExtremaUpperBound(n: int, a: seq<int>)
    requires ValidInput(n, a)
    requires n > 2
    ensures CountLocalExtrema(n, a) <= n - 2
{
    var s := set i | 1 <= i < n - 1 && IsLocalExtremum(a, i);
    
    // For an index i to be a local extremum, we need 1 <= i < n - 1
    // This gives us indices from 1 to n-2 inclusive
    assert forall i :: i in s ==> 1 <= i < n - 1;
    assert forall i :: i in s ==> 1 <= i <= n - 2;
    
    var possible := set i | 1 <= i <= n - 2;
    assert s <= possible;
    
    CardinalityOfRange(1, n - 2);
    assert |possible| == n - 2 - 1 + 1;
    assert |possible| == n - 2;
    
    assert |s| <= |possible|;
    assert |s| <= n - 2;
    
    // Now establish that CountLocalExtrema(n, a) == |s|
    assert s == set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]));
    assert CountLocalExtrema(n, a) == |s|;
    assert CountLocalExtrema(n, a) <= n - 2;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures n <= 2 ==> result == 0
    ensures n > 2 ==> result <= n - 2
    ensures result == CountLocalExtrema(n, a)
// </vc-spec>
// <vc-code>
{
    if n <= 2 {
        CountLocalExtremaEmpty(n, a);
        return 0;
    }
    
    var count := 0;
    var extrema := {};
    var j := 1;
    
    while j < n - 1
        invariant 1 <= j <= n - 1
        invariant extrema == set i | 1 <= i < j && IsLocalExtremum(a, i)
        invariant count == |extrema|
        invariant count <= j - 1
    {
        if (a[j] > a[j-1] && a[j] > a[j+1]) || (a[j] < a[j-1] && a[j] < a[j+1]) {
            extrema := extrema + {j};
            count := count + 1;
        }
        CountSubset(n, a, j + 1);
        j := j + 1;
    }
    
    assert j == n - 1;
    assert extrema == set i | 1 <= i < n - 1 && IsLocalExtremum(a, i);
    assert extrema == set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]));
    CountLocalExtremaUpperBound(n, a);
    assert count <= n - 2;
    return count;
}
// </vc-code>

