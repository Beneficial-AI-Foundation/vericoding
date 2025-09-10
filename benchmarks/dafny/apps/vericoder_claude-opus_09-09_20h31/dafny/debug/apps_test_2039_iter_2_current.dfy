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
    ensures |set i | 1 <= i < k && IsLocalExtremum(a, i)| <= k - 1
{
    var s := set i | 1 <= i < k && IsLocalExtremum(a, i);
    assert forall i :: i in s ==> 1 <= i < k;
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
    {
        if (a[j] > a[j-1] && a[j] > a[j+1]) || (a[j] < a[j-1] && a[j] < a[j+1]) {
            extrema := extrema + {j};
            count := count + 1;
        }
        j := j + 1;
    }
    
    assert extrema == set i | 1 <= i < n - 1 && IsLocalExtremum(a, i);
    assert extrema == set i | 1 <= i < n - 1 && ((a[i] > a[i-1] && a[i] > a[i+1]) || (a[i] < a[i-1] && a[i] < a[i+1]));
    return count;
}
// </vc-code>

