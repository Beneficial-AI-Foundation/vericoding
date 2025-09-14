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
method IsPrime?(n: nat) returns (answer: Answer) 
      ensures database.Keys == old(database.Keys)
      ensures (n in database) && prime(n) <==> answer == Yes 
      ensures (n in database) && !prime(n) <==> answer == No 
      ensures !(n in database) <==> answer == Unknown
{
  if n in database {
    if database[n] {
      answer := Yes;
    } else {
      answer := No;
    }
  } else {
    answer := Unknown;
  }
}
// </vc-helpers>

// <vc-spec>
method testPrimeness(n: nat) returns (result: bool) 
      requires n >= 0
      ensures result <==> prime(n)
// </vc-spec>
// <vc-code>
{
  if n <= 1 {
    result := false;
    return;
  }

  var i := 2;
  while i < n
    decreases n - i
    invariant 2 <= i <= n
    invariant forall j :: 2 <= j < i ==> n % j != 0
  {
    if n % i == 0 {
      result := false;
      return;
    }
    i := i + 1;
  }

  // no divisor found in 2..n-1
  result := true;
}
// </vc-code>

