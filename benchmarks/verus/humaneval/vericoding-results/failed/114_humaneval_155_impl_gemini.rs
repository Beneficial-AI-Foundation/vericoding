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
/* helper modified by LLM (iteration 3): proves total digits is sum of even and odd digits */
proof fn lemma_total_digits(n: nat)
    ensures
        count_even_digits(n) + count_odd_digits(n) == count_digits(n),
    decreases n
{
    if n >= 10 {
        lemma_total_digits(n / 10);
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
    /* code modified by LLM (iteration 3): fixed compilation error (invalid ghost block syntax) */
    let ghost n_abs = abs_value(num as int);

    if num == 0 {
        lemma_total_digits(0);
        return (1, 0);
    }

    let mut n_exec = if num < 0 { (-(num as i16)) as u32 } else { num as u32 };
    assert(n_exec as nat == n_abs);
    
    let mut even_c: i8 = 0;
    let mut odd_c: i8 = 0;
    
    let ghost mut temp_n_ghost = n_abs;

    while n_exec >= 10
        invariant
            num != 0,
            n_abs == abs_value(num as int),
            n_abs > 0,
            n_exec > 0,
            temp_n_ghost > 0,
            n_exec as nat == temp_n_ghost,
            count_even_digits(n_abs) == (even_c as nat) + count_even_digits(temp_n_ghost),
            count_odd_digits(n_abs) == (odd_c as nat) + count_odd_digits(temp_n_ghost),
        decreases n_exec
    {
        let digit = n_exec % 10;
        assert(is_even_digit(temp_n_ghost % 10) <==> digit % 2 == 0);

        if digit % 2 == 0 {
            even_c = even_c + 1;
        } else {
            odd_c = odd_c + 1;
        }
        n_exec = n_exec / 10;
        proof { temp_n_ghost = temp_n_ghost / 10; }
    }

    assert(n_exec < 10);
    assert(temp_n_ghost < 10);
    assert(is_even_digit(temp_n_ghost) <==> n_exec % 2 == 0);

    let final_even_c = if n_exec % 2 == 0 { even_c + 1 } else { even_c };
    let final_odd_c = if n_exec % 2 != 0 { odd_c + 1 } else { odd_c };
    
    lemma_total_digits(n_abs);
    (final_even_c, final_odd_c)
}
// </vc-code>


}

fn main() {}