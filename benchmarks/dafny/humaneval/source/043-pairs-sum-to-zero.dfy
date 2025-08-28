method pairs_sum_to_zero(l : seq<int>) returns (result : bool)
   // post-conditions-start
    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
    // post-conditions-end
{
    // impl-start
    result := false;
    var i : int := 0;
    while i < |l|
        // invariants-start
        invariant i >= 0 && i <= |l|
        invariant !result ==> forall i1 : int, j : int :: 0 <= i1 < i && 0 <= j < |l| && i1 != j ==> l[i1] + l[j] != 0
        invariant result ==> exists i1 : int, j : int :: 0 <= i1 < i && 0 <= j < |l| && i1 != j && l[i1] + l[j] == 0
        // invariants-end
    {
        var j : int := 0;
        while j < |l|
            // invariants-start
            invariant j >= 0 && j <= |l|
            invariant !result ==> forall i1 : int, j : int :: 0 <= i1 < i && 0 <= j < |l| && i1 != j ==> l[i1] + l[j] != 0
            invariant !result ==> forall j1 : int :: 0 <= j1 < j && i != j1 ==> l[i] + l[j1] != 0
            invariant result ==> (exists i1 : int, j1 : int :: 0 <= i1 < i && 0 <= j1 < |l| && i1 != j1 && l[i1] + l[j1] == 0) || (exists j1 : int :: 0 <= j1 < j && i != j1 && l[i] + l[j1] == 0)
            // invariants-end
        {
            if i != j && l[i] + l[j] == 0 {
                result := true;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    // impl-end
}
