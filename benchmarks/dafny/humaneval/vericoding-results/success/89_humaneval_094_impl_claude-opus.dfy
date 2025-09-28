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
predicate has_prime(lst: seq<int>)
{
    exists x :: x in lst && is_prime_pure(x)
}

function find_largest_prime(lst: seq<int>): int
    requires has_prime(lst)
    ensures find_largest_prime(lst) in lst
    ensures is_prime_pure(find_largest_prime(lst))
    ensures forall y :: y in lst && is_prime_pure(y) ==> y <= find_largest_prime(lst)
{
    if |lst| == 1 then
        lst[0]
    else if |lst| == 0 then
        0  // This case won't be reached due to precondition
    else
        var rest_has_prime := has_prime(lst[1..]);
        if rest_has_prime then
            var rest_largest := find_largest_prime(lst[1..]);
            if is_prime_pure(lst[0]) && lst[0] >= rest_largest then
                lst[0]
            else
                rest_largest
        else if is_prime_pure(lst[0]) then
            lst[0]
        else
            lst[0]  // This case won't be reached due to precondition
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
    var has_any_prime := false;
    var largest_prime := 0;
    var i := 0;
    
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant !has_any_prime ==> (forall j :: 0 <= j < i ==> !is_prime_pure(lst[j]))
        invariant has_any_prime ==> (exists j :: 0 <= j < i && lst[j] == largest_prime && is_prime_pure(largest_prime))
        invariant has_any_prime ==> (forall j :: 0 <= j < i && is_prime_pure(lst[j]) ==> lst[j] <= largest_prime)
    {
        if is_prime_pure(lst[i]) {
            if !has_any_prime || lst[i] > largest_prime {
                largest_prime := lst[i];
                has_any_prime := true;
            }
        }
        i := i + 1;
    }
    
    if has_any_prime {
        result := sum_of_digits(largest_prime);
    } else {
        result := 0;
    }
}
// </vc-code>
