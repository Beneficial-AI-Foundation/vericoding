

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
    if |l| < 3 {
        return false;
    }
    for i := 0; i < |l|; i := i + 1 {
        invariant 0 <= i <= |l|
        invariant forall i2, j, k :: 0 <= i2 < i && i2 < j < k < |l| ==> l[i2] + l[j] + l[k] != 0
        for j := i + 1; j < |l|; j := j + 1 {
            invariant i < j <= |l|
            invariant forall j2, k :: i < j2 < j && j2 < k < |l| ==> l[i] + l[j2] + l[k] != 0
            for k := j + 1; k < |l|; k := k + 1 {
                invariant j < k <= |l|
                invariant forall k2 :: j < k2 < k ==> l[i] + l[j] + l[k2] != 0
                if l[i] + l[j] + l[k] == 0 {
                    return true;
                }
            }
        }
    }
    return false;
}
// </vc-code>

