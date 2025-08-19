predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}

predicate IsPrime(i:nat)
{
  && 1<i
  && ( forall f :: 1 < f < i ==> !divides(f, i) )
}

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method test_prime(i:nat) returns (result:bool)
  requires 1<i
  ensures result == IsPrime(i)
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>