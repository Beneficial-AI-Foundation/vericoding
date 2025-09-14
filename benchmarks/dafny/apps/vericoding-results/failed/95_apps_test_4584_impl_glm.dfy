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

// <vc-helpers>
function PrefixSubordinateCount(aa: seq<int>, boss_id: int, prefix: int): int
    requires 0 <= prefix <= |aa|
{
    |set j | 0 <= j < prefix && aa[j] == boss_id|
}

lemma PrefixSubordinateCountStep(aa: seq<int>, boss_id: int, i: int)
    requires 0 <= i < |aa|
    ensures PrefixSubordinateCount(aa, boss_id, i+1) == 
            PrefixSubordinateCount(aa, boss_id, i) + (if aa[i] == boss_id then 1 else 0)
{
    calc {
        PrefixSubordinateCount(aa, boss_id, i+1);
    ==  // definition
        |set j | 0 <= j < i+1 && aa[j] == boss_id|;
    ==  // split the set at j = i
        |set j | 0 <= j < i && aa[j] == boss_id| + |set j | j == i && aa[j] == boss_id|;
    ==  // the second set is either 0 or 1
        PrefixSubordinateCount(aa, boss_id, i) + (if aa[i] == boss_id then 1 else 0);
    }
}

lemma LemmaFullPrefix(aa: seq<int>, n: int)
    requires ValidInput(n, aa)
    ensures forall boss_id :: 1 <= boss_id <= n ==> 
            PrefixSubordinateCount(aa, boss_id, |aa|) == SubordinateCount(aa, boss_id)
{
    forall boss_id | 1 <= boss_id <= n
        ensures PrefixSubordinateCount(aa, boss_id, |aa|) == SubordinateCount(aa, boss_id)
    {
        calc {
            PrefixSubordinateCount(aa, boss_id, |aa|);
        ==  // definition of PrefixSubordinateCount
            |set j | 0 <= j < |aa| && aa[j] == boss_id|;
        ==  // definition of SubordinateCount
            SubordinateCount(aa, boss_id);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
// </vc-spec>
// <vc-code>
{
    var res := new int[n];
    var i := 0;
    while i < n-1
        invariant 0 <= i <= n-1
        invariant forall k :: 0 <= k < n ==> res[k] >= 0
        invariant forall boss_id {:trigger PrefixSubordinateCount(aa, boss_id, i)} :: 
                 1 <= boss_id <= n ==> 
                 res[boss_id-1] == PrefixSubordinateCount(aa, boss_id, i)
    {
        var boss: int := aa[i];
        var old_count := res[boss-1];
        res[boss-1] := old_count + 1;
        
        assert forall boss_id :: 1 <= boss_id <= n ==> 
            res[boss_id-1] == PrefixSubordinateCount(aa, boss_id, i+1);
        {
            forall boss_id | 1 <= boss_id <= n
            {
                if boss_id == boss {
                    calc {
                        res[boss_id-1];
                    ==  res[boss-1];
                    ==  old_count + 1;
                    ==  PrefixSubordinateCount(aa, boss, i) + 1;
                    ==  { PrefixSubordinateCountStep(aa, boss, i) }
                        PrefixSubordinateCount(aa, boss, i+1);
                    }
                } else {
                    calc {
                        res[boss_id-1];
                    ==  old_count;
                    ==  PrefixSubordinateCount(aa, boss_id, i);
                    ==  { PrefixSubordinateCountStep(aa, boss_id, i); 
                          assert aa[i] != boss_id; }
                        PrefixSubordinateCount(aa, boss_id, i+1);
                    }
                }
            }
        }
        
        i := i + 1;
    }
    LemmaFullPrefix(aa, n);
    result := res[..];
}
// </vc-code>

