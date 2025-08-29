// <vc-helpers>
lemma DivisibleImpliesNotPrime(k: int, j: int)
  requires k >= 2
  requires 2 <= j < k
  requires k % j == 0
  ensures exists i :: 2 <= i < k && k % i == 0
{
}
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
method IsPrime(k: int) returns (result: bool)
  requires k >= 2
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
{
  result := true;
  var i := 2;
  while i < k
    invariant 2 <= i <= k
    invariant result ==> forall j :: 2 <= j < i ==> k % j != 0
  {
    if k % i == 0 {
      result := false;
      DivisibleImpliesNotPrime(k, i);
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
