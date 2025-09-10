predicate ValidInput(n: int, p: seq<int>)
{
    |p| == n && n >= 3
}

function CountMedianElements(p: seq<int>, n: int): int
    requires ValidInput(n, p)
{
    |set i | 0 <= i < n - 2 && IsMedianOfThree(p[i], p[i + 1], p[i + 2]) :: i|
}

predicate IsMedianOfThree(a: int, b: int, c: int)
{
    (a < b < c) || (a > b > c)
}

// <vc-helpers>
lemma CountMedianElementsLemma(p: seq<int>, n: int, k: int)
    requires ValidInput(n, p)
    requires 0 <= k <= n - 2
    ensures |set i | 0 <= i < k && IsMedianOfThree(p[i], p[i + 1], p[i + 2]) :: i| <= k
{
    var s := set i | 0 <= i < k && IsMedianOfThree(p[i], p[i + 1], p[i + 2]) :: i;
    var all := set i | 0 <= i < k :: i;
    
    // Prove that s is a subset of all
    forall x | x in s
        ensures x in all
    {
        // If x is in s, then 0 <= x < k and IsMedianOfThree holds
        // Therefore x is in all
    }
    
    // Prove that |all| == k by induction
    if k == 0 {
        assert all == {};
        assert |all| == 0;
    } else {
        var all_prev := set i | 0 <= i < k - 1 :: i;
        assert all == all_prev + {k - 1};
        assert k - 1 !in all_prev;
        assert |all| == |all_prev| + 1;
        // By induction hypothesis, |all_prev| == k - 1
        CardinalityHelper(k - 1);
        assert |all_prev| == k - 1;
        assert |all| == k;
    }
    
    // Since s is a subset of all and |all| == k, we have |s| <= k
    assert s <= all;
    CardinalitySubset(s, all);
}

lemma CardinalityHelper(k: nat)
    ensures |set i | 0 <= i < k :: i| == k
{
    if k == 0 {
        assert set i | 0 <= i < 0 :: i == {};
    } else {
        var s_prev := set i | 0 <= i < k - 1 :: i;
        var s := set i | 0 <= i < k :: i;
        assert s == s_prev + {k - 1};
        assert k - 1 !in s_prev;
        CardinalityHelper(k - 1);
        assert |s_prev| == k - 1;
        assert |s| == |s_prev| + 1 == k;
    }
}

lemma CardinalitySubset<T>(s: set<T>, t: set<T>)
    requires s <= t
    ensures |s| <= |t|
{
    // This is a built-in property in Dafny
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: seq<int>) returns (result: int)
    requires ValidInput(n, p)
    ensures result >= 0
    ensures result <= n - 2
    ensures result == CountMedianElements(p, n)
// </vc-spec>
// <vc-code>
{
    var count := 0;
    var i := 0;
    
    while i < n - 2
        invariant 0 <= i <= n - 2
        invariant 0 <= count <= i
        invariant count == |set j | 0 <= j < i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j|
    {
        var prev_set := set j | 0 <= j < i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j;
        
        if IsMedianOfThree(p[i], p[i + 1], p[i + 2]) {
            count := count + 1;
            var new_set := set j | 0 <= j < i + 1 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j;
            assert new_set == prev_set + {i};
            assert |new_set| == |prev_set| + 1;
        } else {
            var new_set := set j | 0 <= j < i + 1 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j;
            assert new_set == prev_set;
        }
        
        CountMedianElementsLemma(p, n, i + 1);
        i := i + 1;
    }
    
    assert i == n - 2;
    assert count == |set j | 0 <= j < n - 2 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j|;
    result := count;
}
// </vc-code>

