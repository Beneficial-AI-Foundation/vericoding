method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result ==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result ==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
{
  assume{:axiom} false;
}
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}

// <vc-helpers>
method is_prime(k: int) returns (result: bool)
  // pre-conditions-start
  requires k >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> forall i :: 2 <= i < k ==> k % i != 0
  ensures !result <==> exists j :: 2 <= j < k && k % j == 0
  // post-conditions-end
{
  var j := 2;
  while j * j <= k
    invariant j > 1
    invariant forall h :: 2 <= h < j ==> k % h != 0
    decreases k - j + 1
  {
    if k % j == 0 {
      result := false;
      return;
    }
    j := j + 1;
  }
  result := true;
}
function is_prime_pred(k: int) : bool
{
  forall i :: 2 <= i < k ==> k % i != 0
}
// </vc-helpers>

// <vc-spec>
method largest_prime_factor(n: int) returns (largest: int)
  // pre-conditions-start
  requires n >= 2
  // pre-conditions-end
  // post-conditions-start
  ensures 1 <= largest <= n && (largest == 1 || (largest > 1 && is_prime_pred(largest)))
  // post-conditions-end
// </vc-spec>
// <vc-code>
largest := 1;
  var m := n;
  var i := 2;
  while i * i <= m
    invariant 1 <= largest <= n
    invariant largest == 1 || (largest > 1 && forall j :: 2 <= j < largest ==> largest % j != 0)
    invariant i >= 2
    decreases n - m + (n - i + 1)
  {
    if m % i == 0
    {
      largest := i;
      while m % i == 0
        invariant m >= 1
        invariant largest == i
      {
        m := m / i;
      }
    }
    if i == 2 {
      i := 3;
    } else {
      i := i + 2;
    }
  }
  if m > 1
  {
    largest := m;
  }
// </vc-code>

