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
function is_prime_pred(k: int) : bool
{
  k >= 2 && forall i :: 2 <= i < k ==> k % i != 0
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
{
  var current_n := n;
  largest := 1;

  var j := 2;
  while j * j <= current_n
    invariant 2 <= j || j == 2
    invariant current_n >= 1
    invariant largest >= 1
    invariant forall i :: 2 <= i < j && current_n % i != 0 ==> n % i != 0 // No remaining common factors below j
    invariant forall f :: is_prime_pred(f) && f <= largest ==> n % f == 0 // All prime factors less than or equal to largest also divide n (initially largest=1, vacuous)
    invariant forall f :: is_prime_pred(f) && f <= largest ==> is_prime_pred(f) && n % f == 0
    invariant n % current_n == 0
    decreases current_n
  {
    if current_n % j == 0 {
      largest := j;
      while current_n % j == 0
        invariant largest == j
        invariant n % current_n == 0
        invariant current_n >= 1
      {
        current_n := current_n / j;
      }
    }
    j := j + 1;
  }

  if current_n > 1 {
    largest := current_n;
  }
}
// </vc-code>

