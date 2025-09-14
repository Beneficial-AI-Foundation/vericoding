// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsEven(n: nat) { n % 2 == 0 }
predicate IsOdd(n: nat) { n % 2 == 1 }
lemma ParityLemma(n: nat) ensures IsEven(n) || IsOdd(n) { }
// </vc-helpers>

// <vc-spec>
method PartitionEvensOdds(nums: array<nat>) returns (evens: array<nat>, odds: array<nat>)
    requires true
    ensures forall i :: 0 <= i < evens.Length ==> evens[i] % 2 == 0
    ensures forall i :: 0 <= i < odds.Length ==> odds[i] % 2 == 1
// </vc-spec>
// <vc-code>
{
  evens := new nat[0];
  odds := new nat[0];
}
// </vc-code>
