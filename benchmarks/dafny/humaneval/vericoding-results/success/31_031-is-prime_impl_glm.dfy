// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
    invariant forall j :: 2 <= j < i ==> k % j != 0
  {
    if k % i == 0 {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>
