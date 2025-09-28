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
fn count_even_odd_digits_recursive(n: u8) -> (even: i8, odd: i8)
    ensures 
        even >= 0 && odd >= 0 &&
        even + odd >= 1 &&
        even as nat == count_even_digits(n as nat) &&
        odd as nat == count_odd_digits(n as nat) &&
        even + odd == count_digits(n as nat) as i8
    decreases n
{
    if n < 10 {
        if n % 2 == 0 {
            (1, 0)
        } else {
            (0, 1)
        }
    } else {
        let digit = n % 10;
        let (even_rest, odd_rest) = count_even_odd_digits_recursive(n / 10);
        if digit % 2 == 0 {
            (even_rest + 1, odd_rest)
        } else {
            (even_rest, odd_rest + 1)
        }
    }
}
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
{
    let abs_num = if num < 0 { (num as i32).abs() as u8 } else { num as u8 };
    count_even_odd_digits_recursive(abs_num)
}
// </vc-code>


}

fn main() {}