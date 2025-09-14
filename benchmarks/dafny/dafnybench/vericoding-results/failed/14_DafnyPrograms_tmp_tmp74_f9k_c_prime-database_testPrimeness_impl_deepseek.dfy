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
lemma prime_implies_nonzero(n: nat)
  requires prime(n)
  ensures n > 0
{
}

lemma prime_implies_positive(n: nat)
  requires prime(n)
  ensures n >= 2
{
}

lemma prime_one_not_prime(n: nat)
  requires n == 1
  ensures !prime(n)
{
}

lemma prime_zero_not_prime(n: nat)
  requires n == 0
  ensures !prime(n)
{
}

lemma prime_test_helper(n: nat)
  requires n >= 2
  ensures prime(n) <==> (forall nr | 1 < nr < n :: n % nr != 0)
{
}

lemma mod_zero_implies_divisor(n: nat, d: nat)
  requires d > 0 && d <= n
  requires n % d == 0
  ensures exists q :: n == d * q
{
  var q := n / d;
  assert n == d * q;
}

ghost predicate prime_alt(n: nat)
  ensures prime_alt(n) <==> prime(n)
{
  n > 1 && (forall nr | 1 < nr < n :: n % nr != 0)
}

lemma prime_alt_implies_prime(n: nat)
  requires prime_alt(n)
  ensures prime(n)
{
}

lemma prime_implies_prime_alt(n: nat)
  requires prime(n)
  ensures prime_alt(n)
{
}

lemma prime_alt_equivalence(n: nat)
  ensures prime_alt(n) <==> prime(n)
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method testPrimeness(n: nat) returns (result: bool) 
      requires n >= 0
      ensures result <==> prime(n)
// </vc-spec>
// <vc-code>
{
  if n < 2 {
    if n == 0 {
      prime_zero_not_prime(n);
    } else if n == 1 {
      prime_one_not_prime(n);
    }
    return false;
  }
  
  var i := 2;
  while i < n
    invariant 2 <= i <= n + 1
    invariant forall k | 2 <= k < i :: n % k != 0
    decreases n - i
  {
    if n % i == 0 {
      mod_zero_implies_divisor(n, i);
      return false;
    }
    i := i + 1;
  }
  assert prime_alt(n);
  prime_alt_implies_prime(n);
  return true;
}
// </vc-code>

