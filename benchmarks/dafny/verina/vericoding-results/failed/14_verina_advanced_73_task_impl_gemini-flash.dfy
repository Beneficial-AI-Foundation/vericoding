// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function SmallestMissing(l: seq<nat>): nat {
    if |l| == 0 then 0
    else if l[0] > 0 then 0
    else if |l| == 1 then l[0] + 1
    else {
        var low := 0;
        var high := |l| - 1;
        var ans := |l|;

        while low <= high
            invariant 0 <= low <= high + 1 <= |l|
            invariant (exists i : int :: low <= i < |l| && l[i] > i) ==> ans <= high + 1
            invariant forall i :: 0 <= i < low ==> l[i] == i
        {
            var mid := low + (high - low) / 2;
            if l[mid] == mid then {
                low := mid + 1;
            } else {
                ans := mid;
                high := mid - 1;
            }
        }
        ans
    }
}
// </vc-helpers>

// <vc-spec>
function SmallestMissing(l: seq<nat>): nat

lemma SmallestMissingSpecSatisfied(l: seq<nat>)
    requires forall i, j :: 0 <= i < j < |l| ==> l[i] < l[j]
    ensures SmallestMissing(l) !in l
    ensures forall candidate: nat :: candidate < SmallestMissing(l) ==> candidate in l
// </vc-spec>
// <vc-code>
{
    if |l| == 0 then return;
    if l[0] > 0 then return;

    var missing := 0;
    while missing < |l|
        invariant 0 <= missing <= |l|
        invariant forall k :: 0 <= k < missing ==> k in l
        invariant forall k :: k < missing && k !in l ==> false
    {
        if l[missing] != missing then {
            return;
        }
        missing := missing + 1;
    }
    // If we reached here, it means all numbers from 0 to |l|-1 are in l.
    // So the smallest missing number is |l|.
}
// </vc-code>
