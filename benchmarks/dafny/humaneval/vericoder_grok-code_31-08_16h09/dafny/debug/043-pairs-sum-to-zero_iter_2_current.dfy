

// <vc-helpers>
// No additional helpers needed for this verification.
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
    var i := 0;
    while i < |l|
        invariant 0 <= i <= |l|
        invariant forall i' : int :: 0 <= i' < i ==> forall j : int :: 0 <= j < |l| && j != i' ==> l[i'] + l[j] != 0
    {
        var j := 0;
        while j < |l|
            invariant 0 <= j <= |l|
        {
            if i != j && l[i] + l[j] == 0
            {
                return true;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    return false;
}
// </vc-code>

