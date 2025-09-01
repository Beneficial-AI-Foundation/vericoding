

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
    for i := 0 to |l| - 1 {
        invariant 0 <= i <= |l|
        invariant forall i2, j2, k2 :: 0 <= i2 < i && i2 < j2 && j2 < k2 && k2 < |l| ==> l[i2] + l[j2] + l[k2] != 0
        for j := i + 1 to |l| - 1 {
            invariant i < j <= |l|
            invariant forall j2, k2 :: i < j2 && j2 < j && j2 < k2 && k2 < |l| ==> l[i] + l[j2] + l[k2] != 0
            for k := j + 1 to |l| - 1 {
                invariant j < k <= |l|
                invariant forall k2 :: j < k2 && k2 < k ==> l[i] + l[j] + l[k2] != 0
                if l[i] + l[j] + l[k] == 0 {
                    return true;
                }
            }
        }
    }
    return false;
}
// </vc-code>

