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
predicate is_prime(n: nat) {
  n > 1 && (forall nr | 1 < nr < n :: n % nr != 0)
}

predicate no_small_divisors(n: nat, limit: nat) {
  forall k | 5 <= k <= limit && (k % 6 == 5 || k % 6 == 1) :: n % k != 0 && n % (k + 2) != 0
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
        return false;
    }
    if n == 2 || n == 3 {
        return true;
    }
    if n % 2 == 0 || n % 3 == 0 {
        return false;
    }

    var i := 5;
    while (i * i) <= n
        invariant i >= 5
        invariant i % 6 == 5 || i % 6 == 1
        invariant no_small_divisors(n, i - 1)
        invariant forall k | 5 <= k < i && (k % 6 == 5 || k % 6 == 1) :: n % k != 0 && n % (k + 2) != 0
        invariant forall k | 5 <= k < i && (k % 6 == 5 || k % 6 == 1) && n % k == 0 :: false
        invariant forall k | 5 <= k < i && (k % 6 == 5 || k % 6 == 1) && n % (k + 2) == 0 :: false
        invariant forall factor | 5 <= factor < i && (factor % 6 == 5 || factor % 6 == 1 || (factor - 2) % 6 == 5 || (factor - 2) % 6 == 1) && n % factor == 0 :: false
    {
        if n % i == 0 || n % (i + 2) == 0 {
            return false;
        }
        i := i + 6;
    }
    return true;
}
// </vc-code>

