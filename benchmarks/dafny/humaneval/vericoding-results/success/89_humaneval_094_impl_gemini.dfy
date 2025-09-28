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
method is_prime_impl(n: int) returns (b: bool)
    ensures b == is_prime_pure(n)
{
    if n < 2 {
        b := false;
        return;
    }
    var k := 2;
    while k < n
        invariant 2 <= k <= n
        invariant forall j :: 2 <= j < k ==> n % j != 0
        decreases n - k
    {
        if n % k == 0 {
            b := false;
            return;
        }
        k := k + 1;
    }
    b := true;
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
    /* code modified by LLM (iteration 2): [fixed while loop invariant syntax] */
    var largest_prime := -1;
    var i := 0;

    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant largest_prime != -1 ==> (exists j :: 0 <= j < i && lst[j] == largest_prime && is_prime_pure(lst[j]))
        invariant forall j | 0 <= j < i :: is_prime_pure(lst[j]) ==> lst[j] <= largest_prime
    {
        var x := lst[i];
        var is_x_prime := is_prime_impl(x);
        
        if is_x_prime {
            if x > largest_prime {
                largest_prime := x;
            }
        }
        i := i + 1;
    }

    if largest_prime == -1 {
        result := 0;
    } else {
        result := sum_of_digits(largest_prime);
    }
}
// </vc-code>
