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
  k >= 2 && (forall i :: 2 <= i < k ==> k % i != 0)
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
    invariant 2 <= j
    invariant current_n >= 1
    invariant largest >= 1
    invariant n % current_n == 0
    invariant (largest == 1 || is_prime_pred(largest))
    invariant (forall f :: is_prime_pred(f) && largest % f == 0 ==> n % f == 0)
    invariant (forall f :: is_prime_pred(f) && f > largest && n % f == 0 ==> current_n % f != 0)
    // Additional invariant to ensure 'j' is prime when assigned to 'largest'
    // if 'current_n % j == 0'
    invariant (forall x :: 2 <= x < j ==> j % x != 0) || j == 2 // This makes sure j is smallest prime number not divisible by others till j-1
    decreases current_n
  {
    if current_n % j == 0 {
      largest := j;
      while current_n % j == 0
        invariant largest == j
        invariant n % current_n == 0
        invariant current_n >= 1
        decreases current_n
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

