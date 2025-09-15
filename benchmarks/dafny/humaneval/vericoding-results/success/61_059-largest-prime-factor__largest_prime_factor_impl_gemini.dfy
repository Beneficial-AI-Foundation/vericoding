// <vc-preamble>
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}
// </vc-preamble>

// <vc-helpers>
method IsPrime(k: int) returns (res: bool)
  requires k >= 1
  ensures res <==> (k > 1 && is_prime_pred(k))
{
  if k < 2 {
    return false;
  }
  res := true;
  var i := 2;
  while i < k
    invariant 2 <= i <= k
    invariant res <==> (forall j :: 2 <= j < i ==> k % j != 0)
    decreases k - i
  {
    if k % i == 0 {
      res := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method largest_prime_factor(n: int) returns (largest: int)

  requires n >= 2

  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
// </vc-spec>
// <vc-code>
{
  var d := n;
  while d >= 2
    invariant 1 <= d <= n
    decreases d
  {
    if n % d == 0 {
      var is_d_prime := IsPrime(d);
      if is_d_prime {
        largest := d;
        return;
      }
    }
    d := d - 1;
  }
  largest := 1;
}
// </vc-code>
