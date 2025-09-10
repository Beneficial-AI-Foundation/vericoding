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
lemma FiniteSetCardinality(n: int)
    requires n >= 0
    ensures |set i {:trigger} | 0 <= i < n :: i| == n
{
    if n == 0 {
        assert set i | 0 <= i < 0 :: i == set{};
    } else {
        var s := set i | 0 <= i < n :: i;
        var s_prev := set i | 0 <= i < n - 1 :: i;
        assert s == s_prev + {n - 1};
        FiniteSetCardinality(n - 1);
    }
}

lemma SetIncrementCardinality(p: seq<int>, i: int)
    requires i >= 0
    ensures |set j {:trigger IsMedianOfThree(p[j], p[j + 1], p[j + 2])} | 0 <= j < i + 1 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j| == 
            |set j {:trigger IsMedianOfThree(p[j], p[j + 1], p[j + 2])} | 0 <= j < i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j| + 
            (if IsMedianOfThree(p[i], p[i + 1], p[i + 2]) then 1 else 0)
{
    var s_new := set j | 0 <= j < i + 1 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j;
    var s_old := set j | 0 <= j < i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j;
    
    if IsMedianOfThree(p[i], p[i + 1], p[i + 2]) {
        assert s_new == s_old + {i};
        assert i !in s_old;
    } else {
        assert s_new == s_old;
    }
}

lemma CountMedianElementsBound(p: seq<int>, n: int)
    requires ValidInput(n, p)
    ensures CountMedianElements(p, n) >= 0
    ensures CountMedianElements(p, n) <= n - 2
{
    var s := set i {:trigger IsMedianOfThree(p[i], p[i + 1], p[i + 2])} | 0 <= i < n - 2 && IsMedianOfThree(p[i], p[i + 1], p[i + 2]) :: i;
    assert forall i :: i in s ==> 0 <= i < n - 2;
    assert s <= set i {:trigger} | 0 <= i < n - 2 :: i;
    var full_range := set i {:trigger} | 0 <= i < n - 2 :: i;
    FiniteSetCardinality(n - 2);
    assert |full_range| == n - 2;
    assert |s| <= |full_range|;
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
    result := 0;
    var i := 0;
    
    while i < n - 2
        invariant 0 <= i <= n - 2
        invariant result == |set j {:trigger IsMedianOfThree(p[j], p[j + 1], p[j + 2])} | 0 <= j < i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j|
    {
        if IsMedianOfThree(p[i], p[i + 1], p[i + 2]) {
            result := result + 1;
        }
        SetIncrementCardinality(p, i);
        i := i + 1;
    }
    
    assert result == |set j {:trigger IsMedianOfThree(p[j], p[j + 1], p[j + 2])} | 0 <= j < n - 2 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j|;
    CountMedianElementsBound(p, n);
}
// </vc-code>

