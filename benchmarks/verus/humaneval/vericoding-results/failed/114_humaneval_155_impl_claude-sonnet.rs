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
/* helper modified by LLM (iteration 5): fixed digit bounds and lemma implementations */
proof fn lemma_count_digits_positive(n: nat)
    requires n >= 0
    ensures count_digits(n) >= 1
    decreases n
{
    if n < 10 {
        // base case: count_digits(n) = 1
    } else {
        lemma_count_digits_positive(n / 10);
    }
}

proof fn lemma_even_odd_sum(n: nat)
    requires n >= 0
    ensures count_even_digits(n) + count_odd_digits(n) == count_digits(n)
    decreases n
{
    if n < 10 {
        // base case
    } else {
        lemma_even_odd_sum(n / 10);
    }
}

proof fn lemma_abs_value_properties(x: int)
    ensures abs_value(x) == abs_value(-x)
{
    if x >= 0 {
        assert(abs_value(x) == x as nat);
        assert(-x <= 0);
        assert(abs_value(-x) == (-(-x)) as nat);
        assert(-(-x) == x);
    } else {
        assert(x < 0);
        assert(-x > 0);
        assert(abs_value(x) == (-x) as nat);
        assert(abs_value(-x) == (-x) as nat);
    }
}

proof fn lemma_i8_bounds()
    ensures count_digits(127) <= 3
{
    assert(127 < 1000);
    assert(count_digits(127) == 1 + count_digits(12));
    assert(count_digits(12) == 1 + count_digits(1));
    assert(count_digits(1) == 1);
    assert(count_digits(127) == 3);
}

proof fn lemma_counts_bounded(n: nat)
    requires n <= 128
    ensures count_even_digits(n) <= 3 && count_odd_digits(n) <= 3
    decreases n
{
    lemma_i8_bounds();
    lemma_even_odd_sum(n);
    if n <= 127 {
        assert(count_digits(n) <= count_digits(127));
        assert(count_digits(n) <= 3);
    } else {
        assert(n == 128);
        assert(count_digits(128) == 3);
    }
    assert(count_even_digits(n) + count_odd_digits(n) == count_digits(n));
    assert(count_digits(n) <= 3);
}

proof fn lemma_digit_step(old_n: nat, new_n: nat, digit: nat, old_even: nat, old_odd: nat, new_even: nat, new_odd: nat)
    requires
        old_n > 0,
        new_n == old_n / 10,
        digit == old_n % 10,
        digit < 10,
        old_even + count_even_digits(old_n) == count_even_digits(old_n),
        old_odd + count_odd_digits(old_n) == count_odd_digits(old_n)
    ensures
        new_even + count_even_digits(new_n) == count_even_digits(old_n),
        new_odd + count_odd_digits(new_n) == count_odd_digits(old_n)
{}
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
    /* code modified by LLM (iteration 5): fixed invariant maintenance and bounds checking */
    let ghost abs_num = abs_value(num as int);
    
    // Handle i8::MIN (-128) specially since -(-128) overflows i8
    let n_val = if num == -128i8 {
        128u8
    } else if num < 0 {
        (-num) as u8
    } else {
        num as u8
    };
    
    let mut n = n_val;
    let mut even_count: i8 = 0;
    let mut odd_count: i8 = 0;
    
    proof {
        lemma_count_digits_positive(abs_num);
        lemma_even_odd_sum(abs_num);
        lemma_abs_value_properties(num as int);
        lemma_counts_bounded(abs_num);
        assert(n as nat == abs_num);
    }
    
    while n > 0
        invariant
            n as nat <= abs_num,
            even_count >= 0,
            odd_count >= 0,
            even_count <= 3,
            odd_count <= 3,
            even_count as nat + count_even_digits(n as nat) == count_even_digits(abs_num),
            odd_count as nat + count_odd_digits(n as nat) == count_odd_digits(abs_num)
        decreases n
    {
        let digit = n % 10;
        
        proof {
            let old_n = n as nat;
            let new_n = (n / 10) as nat;
            assert(new_n == old_n / 10);
            assert(digit as nat == old_n % 10);
            
            if digit % 2 == 0 {
                assert(is_even_digit(digit as nat));
                assert(count_even_digits(old_n) == 1 + count_even_digits(new_n));
                assert(count_odd_digits(old_n) == count_odd_digits(new_n));
            } else {
                assert(!is_even_digit(digit as nat));
                assert(count_odd_digits(old_n) == 1 + count_odd_digits(new_n));
                assert(count_even_digits(old_n) == count_even_digits(new_n));
            }
        }
        
        if digit % 2 == 0 {
            even_count = even_count + 1;
        } else {
            odd_count = odd_count + 1;
        }
        n = n / 10;
    }
    
    (even_count, odd_count)
}
// </vc-code>


}

fn main() {}