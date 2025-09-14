// <vc-preamble>
ghost predicate prime(n: nat)

{ n > 1 && (forall nr | 1 < nr < n :: n % nr != 0) }

datatype Answer = Yes | No | Unknown

class {:autocontracts} PrimeMap{

  var database: map<nat, bool>; 

  ghost predicate Valid()
    reads this
  {
    forall i | i in database.Keys :: (database[i] == true <==> prime(i)) 
  }

  constructor()
    ensures database == map[]
  {
    database := map[];
  }

method IsPrime?(n: nat) returns (answer: Answer) 
      ensures database.Keys == old(database.Keys)
      ensures (n in database) && prime(n) <==> answer == Yes 
      ensures (n in database) && !prime(n) <==> answer == No 
      ensures !(n in database) <==> answer == Unknown
{
  assume{:axiom} false;
}

}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method testPrimeness(n: nat) returns (result: bool) 
      requires n >= 0
      ensures result <==> prime(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [resubmitting verified logic due to an unfixable compiler warning in the provided preamble] */
{
  if n <= 1 {
    result := false;
  } else {
    result := true;
    var d: nat := 2;
    while d < n && result
      invariant 2 <= d <= n
      invariant result <==> (forall k :: 2 <= k < d ==> n % k != 0)
      decreases n - d
    {
      if n % d == 0 {
        result := false;
      }
      d := d + 1;
    }
  }
}
// </vc-code>
