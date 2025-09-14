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
    ensures |set i | low <= i <= high| == if low <= high then high - low + 1 else 0
{
    if low > high {
        assert (set i | low <= i <= high) == {};
        assert |set i | low <= i <= high| == 0;
    } else {
        var s := set i | low <= i <= high;
        // We need to establish the cardinality through induction or axioms
        // Dafny can often figure this out with the right hints
        assert |s| == high - low + 1;
    }
}

lemma CountSubset(n: int, a: seq<int>, k: int)
    requires ValidInput(n, a)
    requires 1 <= k <= n - 1
    ensures |set i | 1 <= i < k && IsLocalExtremum(a, i)| <= max(0, k - 2)
{
    var s := set i | 1 <= i < k && IsLocalExtremum(a, i);
    
    // For i to be a local extremum, we need 1 <= i < |a| - 1
    // Combined with i < k, we get i < min(k, n-1) = k (since k <= n-1)
    // So the valid range is 1 <= i < k
    // But actually, the maximum valid index is min(k-1, n-2)
    
    assert forall i :: i in s ==> 1 <= i < k && 1 <= i < |a| - 1;
    
    if k <= 2 {
        // If k <= 2, then there are no indices i such that 1 <= i < k
        assert s == {};
        assert |s| == 0;
        assert |s| <= max(0, k - 2);
    } else {
        // k >= 3, so indices can range from 1 to k-1
        // But for local extremum, maximum is actually k-2 (since we need i+1 < k)
        assert forall i :: i in s ==> i <= k - 1;
        
        // The set s is a subset of {1, 2, ..., k-2}
        var possible := set i | 1 <= i <= k - 2;
        assert s <= possible;
        
        CardinalityOfRange(1, k - 2);
        assert |possible| == k - 2 - 1 + 1;
        assert |possible| == k - 2;
        
        assert |s| <= |possible|;
        assert |s| <= k - 2;
        assert |s| <= max(0, k - 2);
    }
}

lemma CountLocalExtremaUpperBound(n: int, a: seq<int>)
    requires ValidInput(n, a)
    requires n > 2
    ensures CountLocalExtrema(n, a) <= n - 2
{
    var s := set i | 1 <= i < n - 1 && IsLocalExtremum(a, i);
    
    // For an index i to be a local extremum, we need 1 <= i < n - 1
    // This gives us indices from 1 to n-2 inclusive
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
        invariant count <= max(0, j - 2)
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

