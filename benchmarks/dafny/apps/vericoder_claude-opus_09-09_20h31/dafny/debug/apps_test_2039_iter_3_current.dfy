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
        assert forall i :: 1 <= i < n - 1 ==> false;
        assert |set i | 1 <= i < n - 1 && IsLocalExtremum(a, i)| == 0;
    }
}

lemma CountSubset(n: int, a: seq<int>, k: int)
    requires ValidInput(n, a)
    requires 1 <= k <= n - 1
    ensures |set i | 1 <= i < k && IsLocalExtremum(a, i)| <= k - 2
{
    var s := set i | 1 <= i < k && IsLocalExtremum(a, i);
    assert forall i :: i in s ==> 1 <= i < k;
    // The set s contains indices from 1 to k-1, and for each index i to be a local extremum,
    // we need 1 <= i < k-1 (since we also need i+1 < |a|), so there are at most k-2 such indices
    assert forall i :: i in s ==> 1 <= i <= k - 2;
    var possible := set i | 1 <= i <= k - 2;
    assert s <= possible;
    assert |possible| == k - 2;
    assert |s| <= |possible|;
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
    assert |possible| == n - 2;
    assert |s| <= |possible|;
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

