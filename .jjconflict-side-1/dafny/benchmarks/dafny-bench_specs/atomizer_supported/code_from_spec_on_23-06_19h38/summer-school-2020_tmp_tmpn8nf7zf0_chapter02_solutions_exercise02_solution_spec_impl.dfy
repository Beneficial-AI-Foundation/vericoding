// ATOM 
predicate divides(f:nat, i:nat)
  requires 1<=f
{
  i % f == 0
}


// ATOM 

predicate IsPrime(i:nat)
{
  && 1<i
  && ( forall f :: 1 < f < i ==> !divides(f, i) )
}


// IMPL test_prime

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(i:nat) returns (result:bool)
  requires 1<i
  ensures result == IsPrime(i)
{
  var f := 2;
  while f < i
    invariant 2 <= f <= i
    invariant forall g :: 1 < g < f ==> !divides(g, i)
  {
    if divides(f, i) {
      assert divides(f, i) && 1 < f < i;
      result := false;
      return;
    }
    f := f + 1;
  }
  assert forall g :: 1 < g < i ==> !divides(g, i);
  result := true;
}


// IMPL Main

method Main()
{
}