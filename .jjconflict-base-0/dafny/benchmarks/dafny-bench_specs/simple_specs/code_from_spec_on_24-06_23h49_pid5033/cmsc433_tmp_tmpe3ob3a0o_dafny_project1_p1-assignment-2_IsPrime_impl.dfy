//IMPL 

// Question 7 (20 points)
//
// Implement, and have Dafny verify, the method IsPrime below, which returns true
// if and only if the given positive integer is prime.

method IsPrime (m : int) returns (isPrime : bool)
  requires m > 0 // m must be greater than 0
  ensures isPrime <==> (m > 1 && forall j : int :: 2 <= j < m ==> m % j != 0) 
	// ensures states that "isPrime is true iff m > 1 && not divisible by [2, m-1)"
{
  if m <= 1 {
    isPrime := false;
    return;
  }
  
  var i := 2;
  isPrime := true;
  
  while i < m
    invariant 2 <= i <= m
    invariant isPrime <==> (forall j : int :: 2 <= j < i ==> m % j != 0)
  {
    if m % i == 0 {
      isPrime := false;
      return;
    }
    i := i + 1;
  }
}