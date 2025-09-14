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
lemma PrimeCharacterization(n: nat)
  ensures prime(n) <==> (n > 1 && (forall k | 2 <= k < n :: n % k != 0))
{
  if n <= 1 {
    assert !prime(n);
  } else {
    assert prime(n) <==> (forall nr | 1 < nr < n :: n % nr != 0);
    assert (forall nr | 1 < nr < n :: n % nr != 0) <==> (forall k | 2 <= k < n :: n % k != 0);
  }
}

lemma SmallPrimes()
  ensures prime(2)
  ensures prime(3)
  ensures !prime(0)
  ensures !prime(1)
  ensures !prime(4)
{
  assert 2 > 1 && (forall nr | 1 < nr < 2 :: 2 % nr != 0);
  assert 3 > 1 && (forall nr | 1 < nr < 3 :: 3 % nr != 0);
  assert 4 % 2 == 0;
}

lemma PrimeByTrialDivision(n: nat)
  requires n > 1
  requires n % 2 != 0 || n == 2
  requires forall k | 2 <= k * k <= n :: n % k != 0
  ensures prime(n)
{
  PrimeCharacterization(n);
  assert forall k | 2 <= k < n :: n % k != 0 by {
    forall k | 2 <= k < n
      ensures n % k != 0
    {
      if k * k <= n {
        assert n % k != 0;
      } else {
        if n % k == 0 {
          var q := n / k;
          assert n == k * q;
          assert q >= 1;
          if q == 1 {
            assert n == k;
            assert k < n;
            assert false;
          } else {
            assert q >= 2;
            assert q * k == n;
            assert q < k by {
              if q >= k {
                assert q * k >= k * k > n;
                assert false;
              }
            }
            assert 2 <= q <= q * k <= n;
            assert q * q <= q * k == n;
            assert n % q == 0;
            assert false;
          }
        }
      }
    }
  };
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
  if n == 2 {
    SmallPrimes();
    return true;
  }
  if n % 2 == 0 {
    PrimeCharacterization(n);
    return false;
  }
  
  var i := 3;
  while i * i <= n
    invariant i >= 3
    invariant i % 2 == 1
    invariant forall k | 2 <= k < i :: n % k != 0
    decreases n - i * i + 1
  {
    if n % i == 0 {
      PrimeCharacterization(n);
      return false;
    }
    i := i + 2;
  }
  
  assert forall k | 2 <= k * k <= n :: n % k != 0;
  PrimeByTrialDivision(n);
  return true;
}
// </vc-code>

