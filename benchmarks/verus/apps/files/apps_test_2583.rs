// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn determine_winner(n: int) -> &'static str
    recommends n >= 1
{
    if n == 1 { "FastestFinger" }
    else if n == 2 { "Ashishgup" }
    else if is_power_of_two(n) { "FastestFinger" }
    else if n % 4 != 2 { "Ashishgup" }
    else if is_limited_prime(n / 2) { "FastestFinger" }
    else { "Ashishgup" }
}

spec fn is_power_of_two(n: int) -> bool
    recommends n >= 1
    decreases n
{
    if n <= 0 { false }
    else { n == 1 || (n % 2 == 0 && is_power_of_two(n / 2)) }
}

spec fn is_limited_prime(p: int) -> bool
    recommends p >= 1
{
    if p <= 1 { false }
    else if p == 2 { true }
    else if p % 2 == 0 { false }
    else { is_limited_prime_helper(p, 3) }
}

spec fn is_limited_prime_helper(p: int, divisor: int) -> bool
    recommends p >= 3 && divisor >= 3 && divisor % 2 == 1
    decreases p - divisor
{
    if divisor * divisor > p { true }
    else if p % divisor == 0 { false }
    else { is_limited_prime_helper(p, divisor + 2) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<int>) -> (result: Vec<&'static str>)
    requires
        input.len() >= 1,
        input[0] >= 1,
        input.len() == input[0] + 1,
        forall|i: int| 1 <= i < input.len() ==> input[i] >= 1,
    ensures
        result.len() == input[0],
        forall|i: int| 0 <= i < result.len() ==> result[i] == "FastestFinger" || result[i] == "Ashishgup",
        forall|i: int| 1 <= i < input.len() ==> result[i - 1] == determine_winner(input[i]),
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}