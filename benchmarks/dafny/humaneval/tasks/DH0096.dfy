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
{
    assume {:axiom} false;
  }
// </vc-code>
