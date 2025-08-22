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


//IMPL test_prime

method test_prime(i:nat) returns (result:bool)
 requires 1<i
 ensures result == IsPrime(i)
{
 var f := 2;
 while f < i
  invariant 2 <= f <= i
  invariant forall k :: 2 <= k < f ==> !divides(k, i)
 {
  if divides(f, i) {
   assert divides(f, i) && 1 < f < i;
   result := false;
   return;
  }
  f := f + 1;
 }
 result := true;
}