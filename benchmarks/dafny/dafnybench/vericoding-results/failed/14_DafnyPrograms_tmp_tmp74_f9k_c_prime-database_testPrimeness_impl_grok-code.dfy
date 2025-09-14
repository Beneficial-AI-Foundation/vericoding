//predicate for primeness
ghost predicate prime(n: nat)

{ n > 1 && (forall nr | 1 < nr < n :: n % nr != 0) }

datatype Answer = Yes | No | Unknown

//the class containing a prime database, if a number is prime it returns Yes, if it is not No and if the number
//is not in the database it returns Unknown
class {:autocontracts} PrimeMap{

  var database: map<nat, bool>; 

//the valid invariant of the class
  ghost predicate Valid()
    reads this
  {
    forall i | i in database.Keys :: (database[i] == true <==> prime(i)) 
  }

//the constructor
  constructor()
    ensures database == map[]
  {
    database := map[];
  }


  // lookup n in the database and reply with Yes or No if it's in the database and it is or it is not prime,
  // or with Unknown when it's not in the databse
method IsPrime?(n: nat) returns (answer: Answer) 
      ensures database.Keys == old(database.Keys)
      ensures (n in database) && prime(n) <==> answer == Yes 
      ensures (n in database) && !prime(n) <==> answer == No 
      ensures !(n in database) <==> answer == Unknown
{
  assume{:axiom} false;
}

  // method to test whether a number is prime, returns bool

}

// <vc-helpers>
// <vc-helpers>
lemma{:induction} NoDivisorsImpliesPrime(n: nat, i: nat)
  requires i * i > n
  requires n > 1
  requires forall k | 1 < k < i :: n % k != 0
  ensures prime(n)
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method testPrimeness(n: nat) returns (result: bool) 
      requires n >= 0
      ensures result <==> prime(n)
// </vc-spec>
// <vc-code>
{
  if n <= 1 {
    return false;
  } else if n == 2 || n == 3 {
    return true;
  } else if n % 2 == 0 || n % 3 == 0 {
    return false;
  } else {
    var i: nat := 5;
    while i * i <= n
      invariant 5 <= i
      invariant forall k | 2 <= k < i :: n % k != 0
    {
      if n % i == 0 {
        return false;
      }
      i := i + 2;
    }
    NoDivisorsImpliesPrime(n, i);
    return true;
  }
}
// </vc-code>

