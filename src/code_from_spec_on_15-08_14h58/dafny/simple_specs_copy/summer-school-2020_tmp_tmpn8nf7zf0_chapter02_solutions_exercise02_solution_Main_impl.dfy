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
  /* code modified by LLM (iteration 1): implemented proper primality test using trial division */
  var f := 2;
  while f < i
    invariant 2 <= f <= i
    invariant forall k :: 1 < k < f ==> !divides(k, i)
  {
    if divides(f, i) {
      result := false;
      /* code modified by LLM (iteration 1): added triggering assert to help proof */
      assert divides(f, i) && 1 < f < i;
      return;
    }
    f := f + 1;
  }
  
  /* code modified by LLM (iteration 1): added triggering assert to establish postcondition */
  assert forall k :: 1 < k < i ==> !divides(k, i);
  result := true;
}


//IMPL 

method Main()
{
 var a := test_prime(3);
 var b := test_prime(4);
 var c := test_prime(5);
}