method triples_sum_to_zero(l : seq<int>) returns (result : bool)
    // post-conditions-start
    ensures result ==> exists i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
    ensures !result ==> forall i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
    // post-conditions-end
{
    // impl-start
    result := false;
    var i : int := 0;
    while i < |l|
        // invariants-start
        invariant i >= 0 && i <= |l|
        invariant !result ==> forall i1 : int, j : int, k : int :: 0 <= i1 < i && 0 <= j < |l| && 0 <= k < |l| && i1 != j && j != k && i1 != k ==> l[i1] + l[j] + l[k] != 0
        invariant result ==> exists i1 : int, j : int, k : int :: 0 <= i1 < i && 0 <= j < |l| && 0 <= k < |l| && i1 != j && j != k && i1 != k && l[i1] + l[j] + l[k] == 0
        // invariants-end
    {
        var j : int := 0;
        while j < |l|
            // invariants-start
            invariant j >= 0 && j <= |l|
            invariant !result ==> forall i1 : int, j : int, k : int :: 0 <= i1 < i && 0 <= j < |l| && 0 <= k < |l| && i1 != j && j != k && i1 != k ==> l[i1] + l[j] + l[k] != 0
            invariant !result ==> forall j1 : int, k : int :: 0 <= j1 < j && 0 <= k < |l| && i != j1 && j1 != k && i != k ==> l[i] + l[j1] + l[k] != 0
            invariant result ==> (exists i1 : int, j : int, k : int :: 0 <= i1 < i && 0 <= j < |l| && 0 <= k < |l| && i1 != j && j != k && i1 != k && l[i1] + l[j] + l[k] == 0) || (exists j1 : int, k : int :: 0 <= j1 < j && 0 <= k < |l| && i != j1 && j1 != k && i != k && l[i] + l[j1] + l[k] == 0)
            // invariants-end
        {
            var k : int := 0;
            while k < |l|
                // invariants-start
                invariant k >= 0 && k <= |l|
                invariant !result ==> forall i1 : int, j : int, k : int :: 0 <= i1 < i && 0 <= j < |l| && 0 <= k < |l| && i1 != j && j != k && i1 != k ==> l[i1] + l[j] + l[k] != 0
                invariant !result ==> forall j1 : int, k : int :: 0 <= j1 < j && 0 <= k < |l| && i != j1 && j1 != k && i != k ==> l[i] + l[j1] + l[k] != 0
                invariant !result ==> forall k1 : int :: 0 <= k1 < k && i != j && j != k1 && i != k1 ==> l[i] + l[j] + l[k1] != 0
                invariant result ==> (exists i1 : int, j : int, k : int :: 0 <= i1 < i && 0 <= j < |l| && 0 <= k < |l| && i1 != j && j != k && i1 != k && l[i1] + l[j] + l[k] == 0) || (exists j1 : int, k : int :: 0 <= j1 < j && 0 <= k < |l| && i != j1 && j1 != k && i != k && l[i] + l[j1] + l[k] == 0) || (exists k1 : int :: 0 <= k1 < k && i != j && j != k1 && i != k1 && l[i] + l[j] + l[k1] == 0)
                // invariants-end
            {
                if i != j && j != k && i != k && l[i] + l[j] + l[k] == 0 {
                    result := true;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    // impl-end
}
