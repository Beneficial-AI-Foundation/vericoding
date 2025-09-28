// <vc-preamble>

predicate is_prime_number(n: int)
{
    n >= 2 && forall k :: 2 <= k < n ==> n % k != 0
}
// </vc-preamble>

// <vc-helpers>
function divides(n: int, k: int): bool { k != 0 && n % k == 0 }
// </vc-helpers>

// <vc-spec>
method is_prime(n: int) returns (result: bool)
    ensures result <==> is_prime_number(n)
// </vc-spec>
// <vc-code>
{
  if n < 2 {
    result := false;
    return;
  }
  var k := 2;
  result := true;
  while k < n
    invariant 2 <= k <= n
    invariant forall j :: 2 <= j < k ==> n % j != 0
    decreases n - k
  {
    if n % k == 0 {
      result := false;
      return;
    }
    k := k + 1;
  }
}

// </vc-code>
