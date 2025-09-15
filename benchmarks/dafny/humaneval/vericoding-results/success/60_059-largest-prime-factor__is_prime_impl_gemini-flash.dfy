// <vc-preamble>
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}
// </vc-preamble>

// <vc-helpers>
function is_not_prime(k: int): bool { exists j :: 2 <= j < k && k % j == 0 }
// </vc-helpers>

// <vc-spec>
method is_prime(k: int) returns (result: bool)

  requires k >= 2

  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
// </vc-spec>
// <vc-code>
{
  var i := 2;
  while i < k
    invariant 2 <= i <= k
    invariant forall x :: 2 <= x < i ==> k % x != 0
  {
    if k % i == 0 {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>
