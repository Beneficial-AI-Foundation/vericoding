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
/* helper modified by LLM (iteration 5): add lemmas for digit count properties */
proof fn lemma_abs_value_nonnegative(x: int)
    ensures abs_value(x) >= 0,
{
}

proof fn lemma_abs_value_symmetric(x: int)
    ensures abs_value(x) == abs_value(-x),
{
}

proof fn lemma_count_digits_positive(n: nat)
    requires n > 0,
    ensures count_digits(n) >= 1,
    decreases n,
{
    if n >= 10 {
        lemma_count_digits_positive(n / 10);
    }
}

proof fn lemma_digit_counts_sum(n: nat)
    ensures count_even_digits(n) + count_odd_digits(n) == count_digits(n),
    decreases n,
{
    if n < 10 {
        if is_even_digit(n) {
            assert(count_even_digits(n) == 1nat);
            assert(count_odd_digits(n) == 0nat);
        } else {
            assert(count_even_digits(n) == 0nat);
            assert(count_odd_digits(n) == 1nat);
        }
        assert(count_digits(n) == 1nat);
    } else {
        lemma_digit_counts_sum(n / 10);
        if is_even_digit(n % 10) {
            assert(count_even_digits(n % 10) == 1nat);
            assert(count_odd_digits(n % 10) == 0nat);
        } else {
            assert(count_even_digits(n % 10) == 0nat);
            assert(count_odd_digits(n % 10) == 1nat);
        }
    }
}

proof fn lemma_digit_count_preserved(n: nat, m: nat)
    requires n == m,
    ensures 
        count_even_digits(n) == count_even_digits(m),
        count_odd_digits(n) == count_odd_digits(m),
        count_digits(n) == count_digits(m),
{
}

proof fn lemma_mod_division(n: nat, d: nat)
    requires d > 0,
    ensures (n / d) as nat * d + (n % d) as nat == n,
{
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
    /* code modified by LLM (iteration 5): fix arithmetic safety and loop invariants */
    let abs_num = if num < 0 { (-(num as i32)) as u32 } else { num as u32 };
    let mut n = abs_num;
    let mut even_count: i8 = 0;
    let mut odd_count: i8 = 0;
    
    if n == 0 {
        proof {
            assert(count_even_digits(0) == 1nat) by {
                assert(is_even_digit(0));
            };
            assert(count_odd_digits(0) == 0nat);
            lemma_digit_counts_sum(0);
        }
        return (1, 0);
    }
    
    proof { 
        lemma_count_digits_positive(n as nat);
        lemma_digit_counts_sum(n as nat);
    }
    
    while n != 0
        invariant
            n >= 0,
            even_count >= 0,
            odd_count >= 0,
            even_count as nat + odd_count as nat == count_digits(abs_num as nat) - count_digits(n as nat),
            even_count as nat == count_even_digits(abs_num as nat) - count_even_digits(n as nat),
            odd_count as nat == count_odd_digits(abs_num as nat) - count_odd_digits(n as nat),
        decreases n,
    {
        let digit = n % 10;
        n = n / 10;
        
        proof {
            assert(digit < 10);
            lemma_digit_counts_sum(n as nat);
            lemma_digit_counts_sum(abs_num as nat);
            if is_even_digit(digit as nat) {
                assert(count_even_digits(abs_num as nat) == count_even_digits(n as nat) + 1nat);
                assert(count_odd_digits(abs_num as nat) == count_odd_digits(n as nat));
            } else {
                assert(count_even_digits(abs_num as nat) == count_even_digits(n as nat));
                assert(count_odd_digits(abs_num as nat) == count_odd_digits(n as nat) + 1nat);
            }
        }
        
        if digit % 2 == 0 {
            even_count = even_count + 1;
        } else {
            odd_count = odd_count + 1;
        }
    }
    
    proof {
        assert(n == 0);
        assert(count_digits(0) == 0nat);
        assert(count_even_digits(0) == 0nat);
        assert(count_odd_digits(0) == 0nat);
        lemma_digit_counts_sum(abs_num as nat);
    }
    
    (even_count, odd_count)
}
// </vc-code>


}

fn main() {}