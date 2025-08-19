//ATOM
predicate divides(f:nat, i:nat)
 requires 1<=f
{
 i % f == 0
}


//ATOM

predicate IsPrime(i:nat)
{
 && 1<i
 && ( forall f :: 1 < f < i ==> !divides(f, i) )
}


//ATOM

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(i:nat) returns (result:bool)
 requires 1<i
 ensures result == IsPrime(i)
{
  result := false;
  assume result ==> IsPrime(i);
  return result;
}


//IMPL 

method Main()
{
 /* code modified by LLM (iteration 1): added assertions to establish preconditions for test_prime calls */
 assert 1 < 3;
 var a := test_prime(3);
 assert 1 < 4;
 var b := test_prime(4);
 assert 1 < 5;
 var c := test_prime(5);
}