function IsPrime(n: nat) : bool
{
  n > 1 &&
  forall k :: 2 <= k < n ==> n % k != 0
}

// <vc-helpers>
// Helper lemma to assist in prime checking if needed
lemma PrimeCheckLemma(n: nat, k: nat)
  ensures k > 1 && k <= n && n % k == 0 ==> !IsPrime(n)
{
  if k > 1 && k <= n && n % k == 0 {
    assert 2 <= k < n ==> n % k != 0;
  }
}
// </vc-helpers>

// <vc-spec>
method x_or_y(n: nat, x: int, y: int) returns (result: int)
  // post-conditions-start
  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
  // post-conditions-end
// </vc-spec>
// <vc-code>
method XOrY(n: nat, x: int, y: int) returns (result: int)
  ensures IsPrime(n) ==> result == x
  ensures !IsPrime(n) ==> result == y
{
  if n <= 1 {
    result := y;
    return;
  }
  
  var k := 2;
  while k < n
    invariant 2 <= k <= n
    invariant forall i :: 2 <= i < k ==> n % i != 0
  {
    if n % k == 0 {
      PrimeCheckLemma(n, k);
      result := y;
      return;
    }
    k := k + 1;
  }
  result := x;
}
// </vc-code>
