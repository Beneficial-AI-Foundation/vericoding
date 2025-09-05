Given a list of integers, determine if there exist two distinct elements at different positions that sum to zero. This task requires implementing an efficient algorithm to check for the existence of such a pair.

// ======= TASK =======
// Given a list of integers, determine if there exist two distinct elements at different positions that sum to zero.

// ======= SPEC REQUIREMENTS =======
predicate HasPairSumToZero(l: seq<int>)
{
    exists i, j :: 0 <= i < j < |l| && l[i] + l[j] == 0
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
method pairs_sum_to_zero(l: seq<int>) returns (result: bool)
    ensures result == HasPairSumToZero(l)
{
    var seen: set<int> := {};
    var i := 0;

    while i < |l|
        invariant 0 <= i <= |l|
        invariant seen == set k | 0 <= k < i :: l[k]
        invariant forall k1, k2 :: 0 <= k1 < k2 < i ==> l[k1] + l[k2] != 0
    {
        var num := l[i];
        if -num in seen {
            assert exists k :: 0 <= k < i && l[k] == -num;
            assert exists k :: 0 <= k < i && l[k] + l[i] == 0;
            return true;
        }
        seen := seen + {num};
        i := i + 1;
    }

    return false;
}
