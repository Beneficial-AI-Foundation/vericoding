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
  result := true;
  var f := 2;
  
  while f < i
    invariant 2 <= f <= i
    invariant result == (forall g :: 1 < g < f ==> !divides(g, i))
  {
    if i % f == 0 {
      result := false;
      assert divides(f, i);
      return;
    }
    f := f + 1;
  }
  
  assert f == i;
  assert result == (forall g :: 1 < g < i ==> !divides(g, i));
}
// </vc-code>