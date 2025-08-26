// <vc-spec>
method InsertNumber(n: nat, database: map<nat, bool>) returns (result: map<nat, bool>)
  requires n >= 2
  ensures prime(n) ==> result == database[n := true]
  ensures !prime(n) ==> result == database[n := false]
// </vc-spec>

// <vc-helpers>
predicate prime(n: nat)
{
  n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-helpers>

// <vc-code>
{
  if prime(n) {
    result := database[n := true];
  } else {
    result := database[n := false];
  }
}
// </vc-code>