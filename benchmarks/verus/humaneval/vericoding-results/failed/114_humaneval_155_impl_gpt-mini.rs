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
/* helper modified by LLM (iteration 2): lemma relating count_even_digits/count_odd_digits to their digit decomposition */
fn count_digits_decompose(n: nat)
    requires
        n >= 0,
    ensures
        count_even_digits(n) == if n < 10 { if is_even_digit(n) { 1nat } else { 0nat } } else { (if is_even_digit(n % 10) { 1nat } else { 0nat }) + count_even_digits(n / 10) },
        count_odd_digits(n) == if n < 10 { if !is_even_digit(n) { 1nat } else { 0nat } } else { (if !is_even_digit(n % 10) { 1nat } else { 0nat }) + count_odd_digits(n / 10) },
    decreases n
{
    if n >= 10 {
        count_digits_decompose(n / 10);
    }
    proof {
        // by unfolding the spec definitions; no further proof steps required
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
    /* code modified by LLM (iteration 2): compute even/odd digit counts using machine integers and prove correctness via invariants and lemmas */
    let orig: i8 = if num < 0 { -num } else { num };
    let mut m: i8 = orig;
    let mut even: i8 = 0;
    let mut odd: i8 = 0;
    if m == 0 {
        even = 1;
        odd = 0;
        return (even, odd);
    }
    while m >= 10
        invariant
            (even as nat) + count_even_digits(m as nat) == count_even_digits(abs_value(num as int)),
            (odd as nat) + count_odd_digits(m as nat) == count_odd_digits(abs_value(num as int)),
        decreases m as nat
    {
        let digit: i8 = (m % 10) as i8;
        proof {
            // use the decomposition lemma for the current m (m >= 10)
            count_digits_decompose(m as nat);
        }
        if digit % 2 == 0 {
            even = even + 1;
        } else {
            odd = odd + 1;
        }
        m = m / 10;
    }
    // now m is a single non-zero digit (1..9), handle it
    if m % 2 == 0 {
        even = even + 1;
    } else {
        odd = odd + 1;
    }
    (even, odd)
}
// </vc-code>


}

fn main() {}