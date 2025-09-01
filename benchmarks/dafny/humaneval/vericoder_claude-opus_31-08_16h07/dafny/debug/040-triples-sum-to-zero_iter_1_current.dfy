

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l : seq<int>) returns (result : bool)
    // post-conditions-start
    ensures result ==> exists i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k && l[i] + l[j] + l[k] == 0
    ensures !result ==> forall i : int, j : int, k : int :: 0 <= i < |l| && 0 <= j < |l| && 0 <= k < |l| && i != j && j != k && i != k ==> l[i] + l[j] + l[k] != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    result := false;
    var i := 0;
    while i < |l| && !result
        invariant 0 <= i <= |l|
        invariant result ==> exists ii : int, jj : int, kk : int :: 0 <= ii < |l| && 0 <= jj < |l| && 0 <= kk < |l| && ii != jj && jj != kk && ii != kk && l[ii] + l[jj] + l[kk] == 0
        invariant !result ==> forall ii : int, jj : int, kk : int :: 0 <= ii < i && 0 <= jj < |l| && 0 <= kk < |l| && ii != jj && jj != kk && ii != kk ==> l[ii] + l[jj] + l[kk] != 0
    {
        var j := 0;
        while j < |l| && !result
            invariant 0 <= j <= |l|
            invariant result ==> exists ii : int, jj : int, kk : int :: 0 <= ii < |l| && 0 <= jj < |l| && 0 <= kk < |l| && ii != jj && jj != kk && ii != kk && l[ii] + l[jj] + l[kk] == 0
            invariant !result ==> forall ii : int, jj : int, kk : int :: (0 <= ii < i && 0 <= jj < |l| && 0 <= kk < |l| || ii == i && 0 <= jj < j && 0 <= kk < |l|) && ii != jj && jj != kk && ii != kk ==> l[ii] + l[jj] + l[kk] != 0
        {
            if i != j {
                var k := 0;
                while k < |l| && !result
                    invariant 0 <= k <= |l|
                    invariant result ==> exists ii : int, jj : int, kk : int :: 0 <= ii < |l| && 0 <= jj < |l| && 0 <= kk < |l| && ii != jj && jj != kk && ii != kk && l[ii] + l[jj] + l[kk] == 0
                    invariant !result ==> forall ii : int, jj : int, kk : int :: (0 <= ii < i && 0 <= jj < |l| && 0 <= kk < |l| || ii == i && 0 <= jj < j && 0 <= kk < |l| || ii == i && jj == j && 0 <= kk < k) && ii != jj && jj != kk && ii != kk ==> l[ii] + l[jj] + l[kk] != 0
                {
                    if k != i && k != j && l[i] + l[j] + l[k] == 0 {
                        result := true;
                    }
                    k := k + 1;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>

