// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method PartitionEvensOdds(nums: array<nat>) returns (evens: array<nat>, odds: array<nat>)
    requires true
    ensures forall i :: 0 <= i < evens.Length ==> evens[i] % 2 == 0
    ensures forall i :: 0 <= i < odds.Length ==> odds[i] % 2 == 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): adjusted loop invariants for verification */
    var evens_s: seq<nat> := [];
    var odds_s: seq<nat> := [];
    var i := 0;
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall k :: 0 <= k < |evens_s| ==> evens_s[k] % 2 == 0
        invariant forall k :: 0 <= k < |odds_s| ==> odds_s[k] % 2 == 1
    {
        var x := nums[i];
        if x % 2 == 0 {
            evens_s := evens_s + [x];
        } else {
            odds_s := odds_s + [x];
        }
        i := i + 1;
    }

    evens := new nat[|evens_s|];
    var j := 0;
    while j < |evens_s|
        invariant 0 <= j <= |evens_s|
        invariant forall k :: 0 <= k < |evens_s| ==> evens_s[k] % 2 == 0
        invariant forall k :: 0 <= k < j ==> evens[k] == evens_s[k]
    {
        evens[j] := evens_s[j];
        j := j + 1;
    }

    odds := new nat[|odds_s|];
    var k := 0;
    while k < |odds_s|
        invariant 0 <= k <= |odds_s|
        invariant forall ix :: 0 <= ix < evens.Length ==> evens[ix] % 2 == 0
        invariant forall ix :: 0 <= ix < |odds_s| ==> odds_s[ix] % 2 == 1
        invariant forall ix :: 0 <= ix < k ==> odds[ix] == odds_s[ix]
    {
        odds[k] := odds_s[k];
        k := k + 1;
    }
}
// </vc-code>
