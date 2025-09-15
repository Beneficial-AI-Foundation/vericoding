// <vc-preamble>
function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)

    requires x > 1

    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by changing `%%` to `%` for modulo operator. Also removed `factors` (not declared) and `ProductOfFactors` (not defined), and replaced with a direct count of prime factors. The logic now correctly checks for exactly three prime factors and handles the `temp_x` value. */
{
    var count_factors := 0;
    var temp_x := x;

    for i := 2 to x
        invariant temp_x * (ProductOfPrimeFactors(x, temp_x, 2, i)) == x
        invariant forall k | 2 <= k < i :: x % k != 0 || Prime(k)
        invariant count_factors <= 3
        decreases x - temp_x, i
    {
        while temp_x % i == 0
            invariant temp_x * (ProductOfPrimeFactors(x, temp_x, 2, i)) == x
            invariant forall k | 2 <= k < i :: x % k != 0 || Prime(k)
            invariant count_factors <= 3
            decreases temp_x
        {
            if !Prime(i) { ans := false; return; }
            if count_factors >= 3 { ans := false; return; } 
            count_factors := count_factors + 1;
            temp_x := temp_x / i;
        }
        if temp_x == 1 { break; }
    }
    ans := count_factors == 3 && temp_x == 1;
}

function ProductOfPrimeFactors(original_x: nat, current_x: nat, lower_bound: nat, upper_bound: nat): nat {
    if lower_bound >= upper_bound then
        1
    else if original_x % lower_bound == 0 && Prime(lower_bound) && (current_x * lower_bound) <= original_x then
        lower_bound * ProductOfPrimeFactors(original_x, current_x * lower_bound, lower_bound + 1, upper_bound)
    else
        ProductOfPrimeFactors(original_x, current_x, lower_bound + 1, upper_bound)
}

// </vc-code>
