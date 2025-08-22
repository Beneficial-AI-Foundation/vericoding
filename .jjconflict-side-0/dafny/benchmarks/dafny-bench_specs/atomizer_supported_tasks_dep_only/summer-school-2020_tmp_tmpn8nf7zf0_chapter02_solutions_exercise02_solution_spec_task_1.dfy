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


// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
// SPEC 

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(i:nat) returns (result:bool)
  requires 1<i
  ensures result == IsPrime(i)
{
}


//ATOM_PLACEHOLDER_Main



