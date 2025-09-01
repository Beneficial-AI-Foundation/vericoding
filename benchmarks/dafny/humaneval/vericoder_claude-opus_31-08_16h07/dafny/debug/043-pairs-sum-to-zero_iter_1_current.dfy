

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l : seq<int>) returns (result : bool)
   // post-conditions-start
    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    result := false;
    var i := 0;
    while i < |l|
        invariant 0 <= i <= |l|
        invariant !result ==> forall i' : int, j' : int :: 0 <= i' < i && 0 <= j' < |l| && i' != j' ==> l[i'] + l[j'] != 0
        invariant result ==> exists i' : int, j' : int :: 0 <= i' < |l| && 0 <= j' < |l| && i' != j' && l[i'] + l[j'] == 0
    {
        var j := 0;
        while j < |l|
            invariant 0 <= j <= |l|
            invariant !result ==> forall i' : int, j' : int :: 0 <= i' < i && 0 <= j' < |l| && i' != j' ==> l[i'] + l[j'] != 0
            invariant !result ==> forall j' : int :: 0 <= j' < j && i != j' ==> l[i] + l[j'] != 0
            invariant result ==> exists i' : int, j' : int :: 0 <= i' < |l| && 0 <= j' < |l| && i' != j' && l[i'] + l[j'] == 0
        {
            if i != j && l[i] + l[j] == 0 {
                result := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

