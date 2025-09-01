

// <vc-helpers>
lemma divisor_lemma(n: int, d: int)
  requires 2 <= d < n
  requires n % d == 0
  ensures exists j :: 2 <= j < n && n % j == 0
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
{
  if k == 2 {
    return true;
  } else {
    var i := 2;
    while i < k
      invariant 2 <= i <= k
      invariant forall j :: 2 <= j < i ==> k % j != 0
    {
      if k % i == 0 {
        divisor_lemma(k, i);
        return false;
      }
      i := i + 1;
    }
    return true;
  }
}
// </vc-code>

