// <vc-preamble>

function is_prime_pure(n: int): bool
{
    n >= 2 && (forall k :: 2 <= k < n ==> n % k != 0)
}

function sum_of_digits_pure(n: int): int
    requires n >= 0
{
    if n < 10 then n else (n % 10) + sum_of_digits_pure(n / 10)
}

function sum_of_digits(n: int): int
    requires n >= 0
    ensures sum_of_digits(n) == sum_of_digits_pure(n)
    ensures sum_of_digits(n) >= 0
{
    if n < 10 then n
    else (n % 10) + sum_of_digits(n / 10)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): ensure prime implies >=2 */
lemma prime_ge_2(n: int)
    requires is_prime_pure(n)
    ensures n >= 2
{
    assert n >= 2;
}

/* helper modified by LLM (iteration 2): sum_of_digits_pure is non-negative */
lemma sum_of_digits_pure_nonneg(n: int)
    requires n >= 0
    ensures sum_of_digits_pure(n) >= 0
    decreases n
{
    if n < 10 {
        assert sum_of_digits_pure(n) == n;
        assert sum_of_digits_pure(n) >= 0;
    } else {
        sum_of_digits_pure_nonneg(n / 10);
        assert sum_of_digits_pure(n) == (n % 10) + sum_of_digits_pure(n / 10);
        assert sum_of_digits_pure(n) >= 0;
    }
}
// </vc-helpers>

// <vc-spec>
method skjkasdkd(lst: seq<int>) returns (result: int)
    ensures result >= 0
    ensures (forall x :: x in lst ==> !is_prime_pure(x)) ==> result == 0
    ensures (exists x :: x in lst && is_prime_pure(x)) ==> 
        (exists largest :: (largest in lst && is_prime_pure(largest) && 
         (forall y :: y in lst && is_prime_pure(y) ==> y <= largest) &&
         result == sum_of_digits_pure(largest)))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): find largest prime and return its sum of digits */
{
  var i := 0;
  var found := false;
  var max := 0;
  ghost var idx := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant found == (exists j :: 0 <= j < i && is_prime_pure(lst[j]))
    invariant found ==> 0 <= idx < i && lst[idx] == max && is_prime_pure(max) && (forall j :: 0 <= j < i && is_prime_pure(lst[j]) ==> lst[j] <= max)
    invariant max >= 0
    decreases |lst| - i
  {
    if is_prime_pure(lst[i]) {
      if !found {
        max := lst[i];
        found := true;
        idx := i;
      } else if lst[i] > max {
        max := lst[i];
        idx := i;
      }
    }
    i := i + 1;
  }
  if found {
    sum_of_digits_pure_nonneg(max);
    result := sum_of_digits_pure(max);
  } else {
    result := 0;
  }
}

// </vc-code>
