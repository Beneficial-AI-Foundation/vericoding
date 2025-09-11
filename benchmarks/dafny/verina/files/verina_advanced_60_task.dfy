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
    // TODO: implement
    evens := new nat[0];
    odds := new nat[0];
}
// </vc-code>
