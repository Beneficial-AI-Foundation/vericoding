// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_value(x: int) -> nat {
    if x < 0 { (-x) as nat } else { x as nat }
}

spec fn count_digits(n: nat) -> nat
    recommends n >= 0
    decreases n
{
    if n < 10 { 1nat } else { 1nat + count_digits(n / 10) }
}

spec fn is_even_digit(d: nat) -> bool
    recommends d < 10
{
    d % 2 == 0
}

spec fn count_even_digits(n: nat) -> nat
    recommends n >= 0
    decreases n
{
    if n < 10 {
        if is_even_digit(n) { 1nat } else { 0nat }
    } else {
        (if is_even_digit(n % 10) { 1nat } else { 0nat }) + count_even_digits(n / 10)
    }
}

spec fn count_odd_digits(n: nat) -> nat
    recommends n >= 0
    decreases n
{
    if n < 10 {
        if !is_even_digit(n) { 1nat } else { 0nat }
    } else {
        (if !is_even_digit(n % 10) { 1nat } else { 0nat }) + count_odd_digits(n / 10)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper section was previously empty, but for proper context, I've added a placeholder to indicate that it's intentionally empty for this turn, as no helpers are introduced or modified. */
// </vc-helpers>

// <vc-spec>
fn even_odd_count(num: i8) -> (result: (i8, i8))
    ensures 
        result.0 >= 0 && result.1 >= 0 &&
        result.0 + result.1 >= 1 &&
        ({
            let abs_num = abs_value(num as int);
            result.0 as nat == count_even_digits(abs_num) &&
            result.1 as nat == count_odd_digits(abs_num)
        }) &&
        result.0 + result.1 == count_digits(abs_value(num as int)) as i8 &&
        (num == 0 ==> (result.0 == 1 && result.1 == 0)) &&
        (abs_value(num as int) == abs_value((-num) as int) ==> 
            (result.0 as nat == count_even_digits(abs_value((-num) as int)) && 
             result.1 as nat == count_odd_digits(abs_value((-num) as int))))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed integer overflow for even_count and odd_count by changing them from `i8` to `int`. Adjusted the loop invariant `even_count as nat + odd_count as nat <= count_digits(abs_value(num as int))` to correctly use `abs_value(n)` for the current `n`. Also simplified an 'ensures' clause related to negative numbers which was redundant. Corrected initial values of even_count and odd_count to `0` for `int` type. Also, introduced `digits_processed` to track total digits processed, and added corresponding invariants to establish relationships with `count_digits`. */
{
    let mut n = num as int;
    let mut even_count: int = 0;
    let mut odd_count: int = 0;
    
    if num == 0 {
        return (1, 0);
    }

    let original_num_abs = abs_value(num as int);
    let mut digits_processed: int = 0;

    while n != 0
        invariant
            even_count >= 0,
            odd_count >= 0,
            digits_processed >= 0,
            abs_value(n) < original_num_abs || n == 0,
            digits_processed <= count_digits(original_num_abs) as int,
            even_count + odd_count == digits_processed,
            even_count as nat == count_even_digits(original_num_abs) - count_even_digits(abs_value(n)),
            odd_count as nat == count_odd_digits(original_num_abs) - count_odd_digits(abs_value(n)),
        decreases abs_value(n)
    {
        let digit = (n % 10) as int;
        if digit % 2 == 0 {
            even_count = even_count + 1;
        } else {
            odd_count = odd_count + 1;
        }
        n = n / 10;
        digits_processed = digits_processed + 1;
    }
    (even_count as i8, odd_count as i8)
}
// </vc-code>


}

fn main() {}