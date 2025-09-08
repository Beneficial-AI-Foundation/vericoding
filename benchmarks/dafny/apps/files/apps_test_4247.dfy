Given a permutation p of integers {1, 2, ..., n}, count how many elements p_i 
(where 1 < i < n) are the median (second smallest) value among the three 
consecutive elements p_{i-1}, p_i, and p_{i+1}.

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

method solve(n: int, p: seq<int>) returns (result: int)
    requires ValidInput(n, p)
    ensures result >= 0
    ensures result <= n - 2
    ensures result == CountMedianElements(p, n)
{
    var count := 0;
    var i := 0;
    while i < n - 2
        invariant 0 <= i <= n - 2
        invariant count >= 0
        invariant count <= i
        invariant count == |set j | 0 <= j < i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j|
    {
        var old_count := count;
        var old_i := i;

        if IsMedianOfThree(p[i], p[i + 1], p[i + 2]) {
            count := count + 1;
            assert count == old_count + 1;
            assert i in set j | 0 <= j < old_i + 1 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j;
        } else {
            assert count == old_count;
            assert i !in set j | 0 <= j < old_i + 1 && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j;
        }

        i := i + 1;

        assert (set j | 0 <= j < i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j) == 
               (set j | 0 <= j < old_i && IsMedianOfThree(p[j], p[j + 1], p[j + 2]) :: j) + 
               (if IsMedianOfThree(p[old_i], p[old_i + 1], p[old_i + 2])
                then {old_i} else {});
    }
    result := count;
}
