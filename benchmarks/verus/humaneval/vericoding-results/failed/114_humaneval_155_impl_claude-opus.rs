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
/* helper modified by LLM (iteration 5): Fixed lemma for i8::MIN case and added helper for digit counting */
proof fn lemma_count_digits_sum(n: nat)
    requires n >= 0
    ensures count_even_digits(n) + count_odd_digits(n) == count_digits(n)
    decreases n
{
    if n < 10 {
        if is_even_digit(n) {
            assert(count_even_digits(n) == 1nat);
            assert(count_odd_digits(n) == 0nat);
        } else {
            assert(count_even_digits(n) == 0nat);
            assert(count_odd_digits(n) == 1nat);
        }
    } else {
        lemma_count_digits_sum(n / 10);
        if is_even_digit(n % 10) {
            assert(count_even_digits(n) == 1nat + count_even_digits(n / 10));
            assert(count_odd_digits(n) == 0nat + count_odd_digits(n / 10));
        } else {
            assert(count_even_digits(n) == 0nat + count_even_digits(n / 10));
            assert(count_odd_digits(n) == 1nat + count_odd_digits(n / 10));
        }
    }
}

proof fn lemma_abs_value_symmetry(x: int)
    ensures abs_value(x) == abs_value(-x)
{
    if x < 0 {
        assert(abs_value(x) == (-x) as nat);
        if x == -128 {
            assert(-x == 128);
            assert(abs_value(-x) == 128nat);
            assert((-x) as nat == 128nat);
        } else {
            assert(-(-x) == x);
            assert(abs_value(-x) == x as nat);
        }
    } else if x > 0 {
        assert(abs_value(x) == x as nat);
        assert(-x < 0);
        assert(abs_value(-x) == (-(-x)) as nat);
        assert(-(-x) == x);
    } else {
        assert(x == 0);
        assert(-x == 0);
    }
}

proof fn lemma_count_digits_bounded(n: nat)
    requires n < 256
    ensures count_digits(n) <= 3,
            count_even_digits(n) <= 3,
            count_odd_digits(n) <= 3
    decreases n
{
    if n < 10 {
        assert(count_digits(n) == 1);
    } else if n < 100 {
        lemma_count_digits_bounded(n / 10);
        assert(count_digits(n) == 1 + count_digits(n / 10));
    } else {
        lemma_count_digits_bounded(n / 10);
        assert(n < 256);
        assert(n / 10 < 26);
        assert(count_digits(n) <= 3);
    }
    lemma_count_digits_sum(n);
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
    /* code modified by LLM (iteration 5): Fixed ghost variable declaration and use proper ghost syntax */
    
    // Handle i8::MIN specially to avoid overflow
    let abs_num_u8: u8 = if num == -128i8 {
        128u8
    } else if num < 0 {
        (-num) as u8
    } else {
        num as u8
    };
    
    let ghost abs_num_spec = abs_value(num as int);
    
    let mut even_count: i8 = 0;
    let mut odd_count: i8 = 0;
    let mut n = abs_num_u8;
    
    if num == 0 {
        even_count = 1;
        odd_count = 0;
    } else {
        proof {
            lemma_count_digits_bounded(abs_num_spec);
            assert(count_even_digits(abs_num_spec) <= 3);
            assert(count_odd_digits(abs_num_spec) <= 3);
        }
        
        while n > 0
            invariant
                0 <= even_count <= 3,
                0 <= odd_count <= 3,
                even_count >= 0,
                odd_count >= 0,
                n >= 0,
                n <= 255,
                even_count as nat + count_even_digits(n as nat) == count_even_digits(abs_num_spec),
                odd_count as nat + count_odd_digits(n as nat) == count_odd_digits(abs_num_spec),
                abs_num_spec == abs_value(num as int),
                n as nat <= abs_num_spec,
            decreases n
        {
            let digit = (n % 10) as i8;
            if digit % 2 == 0 {
                proof {
                    lemma_count_digits_bounded(n as nat);
                    assert(count_even_digits(n as nat) >= 1);
                    assert(even_count as nat + count_even_digits(n as nat) <= count_even_digits(abs_num_spec));
                }
                even_count = even_count + 1;
            } else {
                proof {
                    lemma_count_digits_bounded(n as nat);
                    assert(count_odd_digits(n as nat) >= 1);
                    assert(odd_count as nat + count_odd_digits(n as nat) <= count_odd_digits(abs_num_spec));
                }
                odd_count = odd_count + 1;
            }
            n = n / 10;
        }
    }
    
    proof {
        lemma_count_digits_sum(abs_value(num as int));
        lemma_abs_value_symmetry(num as int);
    }
    
    (even_count, odd_count)
}
// </vc-code>


}

fn main() {}