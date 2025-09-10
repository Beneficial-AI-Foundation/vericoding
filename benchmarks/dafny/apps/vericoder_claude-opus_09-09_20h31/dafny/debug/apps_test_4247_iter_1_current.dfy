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
    assert forall i :: i in s ==> 0 <= i < k;
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
    result := count;
}
// </vc-code>

