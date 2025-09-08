Given N company members with ID numbers 1 to N, where each member (except member 1) has exactly one immediate boss with a smaller ID number.
For member i (where i > 1), their immediate boss is member A_i. Count the number of immediate subordinates for each member.

predicate ValidInput(n: int, aa: seq<int>)
{
    n >= 2 &&
    |aa| == n - 1 &&
    forall i :: 0 <= i < |aa| ==> 1 <= aa[i] < i + 2
}

function SubordinateCount(aa: seq<int>, boss_id: int): int
{
    |set j | 0 <= j < |aa| && aa[j] == boss_id|
}

predicate ValidOutput(n: int, aa: seq<int>, result: seq<int>)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> result[i] >= 0 &&
    forall i :: 0 <= i < n ==> result[i] == SubordinateCount(aa, i + 1)
}

method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
{
    var shain := seq(n, _ => 0);
    for i := 0 to |aa|
        invariant 0 <= i <= |aa|
        invariant |shain| == n
        invariant forall k :: 0 <= k < n ==> shain[k] >= 0
        invariant forall k :: 0 <= k < n ==> shain[k] == |set j | 0 <= j < i && aa[j] == k + 1|
    {
        var a := aa[i];
        assert 1 <= a < i + 2;
        assert 0 <= a - 1 < n;

        // Help Dafny understand the relationship between sets before and after adding element i
        var old_set := set j | 0 <= j < i && aa[j] == a;
        var new_set := set j | 0 <= j < i + 1 && aa[j] == a;
        assert new_set == old_set + {i};
        assert |new_set| == |old_set| + 1;

        // For all other values k+1 != a, the sets remain the same
        assert forall k :: 0 <= k < n && k + 1 != a ==> 
            (set j | 0 <= j < i + 1 && aa[j] == k + 1) == (set j | 0 <= j < i && aa[j] == k + 1);

        shain := shain[a-1 := shain[a-1] + 1];

        // Help prove the invariant for the next iteration
        assert forall k :: 0 <= k < n && k != a - 1 ==> shain[k] == |set j | 0 <= j < i + 1 && aa[j] == k + 1|;
        assert shain[a-1] == |set j | 0 <= j < i + 1 && aa[j] == a|;
    }
    result := shain;
}
