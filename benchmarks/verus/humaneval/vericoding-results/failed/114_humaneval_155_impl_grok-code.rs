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
/* helper modified by LLM (iteration 5): Provided executable helper for counting even digits with proper ensures and body. */
fn exec_count_even_digits(n: nat) -> nat
    ensures n == 0 ==> result == 1,
    count_digits(n) as int <= i8::MAX as int
    decreases n
    where result == count_even_digits(n)
{
    if n < 10 {
        if n % 2 == 0 { 1 } else { 0 }
    } else {
        let last = n % 10;
        (if last % 2 == 0 { 1 } else { 0 }) + exec_count_even_digits(n / 10)
    }
}

/* helper modified by LLM (iteration 5): Provided executable helper for counting odd digits with proper ensures and body. */
fn exec_count_odd_digits(n: nat) -> nat
    ensures n == 0 ==> result == 0,  // for 0, no odd digit, but since even count handles
    count_digits(n) as int <= i8::MAX as int
    decreases n
    where result == count_odd_digits(n)
{
    if n < 10 {
        if n % 2 != 0 { 1 } else { 0 }
    } else {
        let last = n % 10;
        (if last % 2 != 0 { 1 } else { 0 }) + exec_count_odd_digits(n / 10)
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
    /* code modified by LLM (iteration 5): Computed even and odd digit counts using absolute value and helper functions, ensuring casts fit i8. */
    let abs_num = abs_value(num as int);
    let even_count = exec_count_even_digits(abs_num);
    let odd_count = exec_count_odd_digits(abs_num);
    (even_count as i8, odd_count as i8)
}
// </vc-code>


}

fn main() {}