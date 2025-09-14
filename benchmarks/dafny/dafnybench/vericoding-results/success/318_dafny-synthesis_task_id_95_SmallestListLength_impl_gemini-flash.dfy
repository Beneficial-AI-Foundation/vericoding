

// <vc-helpers>
/**
 * Since SmallestListLength concerns finding the smallest length among sub-sequences,
 * and not finding a minimum value in a sequence of integers, the original Lemma_SmallestFromSuffixIsSmallestOverall
 * is not relevant. We'll simplify the helpers to remove this lemma.
 *
 * No specific helper methods are needed for the corrected SmallestListLength implementation,
 * as the invariants in the loop are sufficient for verification.
 */
// </vc-helpers>

// <vc-spec>
method SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
// </vc-spec>
// <vc-code>
{
    var minLength := |s[0]|;
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> minLength <= |s[j]|
        invariant exists j :: 0 <= j < i && minLength == |s[j]|
    {
        if |s[i]| < minLength {
            minLength := |s[i]|;
        }
        i := i + 1;
    }
    return minLength;
}
// </vc-code>

