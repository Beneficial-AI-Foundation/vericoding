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
lemma CountMedianElementsBound(p: seq<int>, n: int)
    requires ValidInput(n, p)
    ensures CountMedianElements(p, n) >= 0
    ensures CountMedianElements(p, n) <= n - 2
{
    var s := set i | 0 <= i < n - 2 && IsMedianOfThree(p[i], p[i + 1], p[i + 2]) :: i;
    assert forall i :: i in s ==> 0 <= i < n - 2;
    assert s <= set i | 0 <= i < n - 2 :: i;
    var full_range := set i | 0 <= i < n - 2 :: i;
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
        invariant result == |set j | 0 <= j < i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j|
    {
        if IsMedianOfThree(p[i], p[i + 1], p[i + 2]) {
            result := result + 1;
        }
        i := i + 1;
    }
    
    assert result == |set j | 0 <= j < n - 2 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j|;
    CountMedianElementsBound(p, n);
}
// </vc-code>

