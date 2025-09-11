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
{
  assume {:axiom} false;
}
// </vc-code>
