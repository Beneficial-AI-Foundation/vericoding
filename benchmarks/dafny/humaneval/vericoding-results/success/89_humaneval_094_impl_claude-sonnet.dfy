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
lemma sum_of_digits_nonnegative(n: int)
    requires n >= 0
    ensures sum_of_digits(n) >= 0
{
    if n < 10 {
        assert sum_of_digits(n) == n >= 0;
    } else {
        sum_of_digits_nonnegative(n / 10);
        assert sum_of_digits(n) == (n % 10) + sum_of_digits(n / 10);
        assert n % 10 >= 0;
        assert sum_of_digits(n / 10) >= 0;
    }
}

/* helper modified by LLM (iteration 2): added decreases clause to fix termination */
function find_largest_prime(lst: seq<int>, i: int): int
    requires 0 <= i <= |lst|
    decreases |lst| - i
    ensures find_largest_prime(lst, i) >= 0
    ensures (forall j :: i <= j < |lst| ==> !is_prime_pure(lst[j])) ==> find_largest_prime(lst, i) == 0
    ensures (exists j :: i <= j < |lst| && is_prime_pure(lst[j])) ==> 
        (exists largest :: (largest in lst[i..] && is_prime_pure(largest) && 
         (forall y :: y in lst[i..] && is_prime_pure(y) ==> y <= largest) &&
         find_largest_prime(lst, i) == largest))
{
    if i >= |lst| then 0
    else if is_prime_pure(lst[i]) then
        var rest := find_largest_prime(lst, i + 1);
        if rest == 0 then lst[i]
        else if lst[i] >= rest then lst[i]
        else rest
    else find_largest_prime(lst, i + 1)
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
{
    var largest_prime := find_largest_prime(lst, 0);
    if largest_prime == 0 {
        result := 0;
    } else {
        result := sum_of_digits(largest_prime);
        sum_of_digits_nonnegative(largest_prime);
    }
}
// </vc-code>
