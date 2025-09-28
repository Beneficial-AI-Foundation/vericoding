// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_to_binary(n: nat) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else { int_to_binary_helper(n) }
}

spec fn int_to_binary_helper(n: nat) -> Seq<char>
    decreases n
{
    if n <= 1 { seq!['1'] }
    else { int_to_binary_helper(n / 2) + (if n % 2 == 1 { seq!['1'] } else { seq!['0'] }) }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_div_mod_range(a: int, b: int)
    requires
        b != 0,
    ensures
        0 <= a % b < b || -b < a % b <= 0,
{
    // Verus built-in knowledge about modulo
}

proof fn lemma_rounding_condition(quotient: int, remainder: int, count: int)
    requires
        count > 0,
        0 <= remainder < count,
    ensures
        remainder * 2 < count ==> quotient == (quotient * count + remainder) / count,
        remainder * 2 > count ==> quotient + 1 == (quotient * count + remainder + count) / count,
        remainder * 2 == count && quotient % 2 == 0 ==> quotient == (quotient * count + remainder) / count,
        remainder * 2 == count && quotient % 2 != 0 ==> quotient + 1 == (quotient * count + remainder + count) / count,
{
    if remainder * 2 < count {
        assert((quotient * count + remainder) / count == quotient);
    } else if remainder * 2 > count {
        assert((quotient * count + remainder + count) / count == quotient + 1);
    } else {
        assert(remainder * 2 == count);
        if quotient % 2 == 0 {
            assert((quotient * count + remainder) / count == quotient);
        } else {
            assert((quotient * count + remainder + count) / count == quotient + 1);
        }
    }
}

/* helper modified by LLM (iteration 5): Added conversion utilities for nat/int operations */
spec fn int_to_nat(x: int) -> nat
    requires x >= 0
    ensures result as int == x
{
    x as nat
}

// </vc-helpers>

// <vc-spec>
fn rounded_avg(n: int, m: int) -> (result: String)
    requires n > 0 && m > 0
    ensures (n > m) ==> (result@ == seq!['-', '1']) &&
            (n <= m) ==> (
        result@.len() >= 3 &&
        result@.subrange(0, 2) == seq!['0', 'b'] &&
        ({
            let count = m - n + 1;
            let total_sum = count * (n + m) / 2;
            let quotient = total_sum / count;
            let remainder = total_sum % count;
            let rounded = if remainder * 2 < count { quotient }
                         else if remainder * 2 > count { quotient + 1 }
                         else if quotient % 2 == 0 { quotient }
                         else { quotient + 1 };
            result@ == seq!['0', 'b'] + int_to_binary(rounded as nat)
        })
    )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer type conversions and indexing */
    if n > m {
        return "-1".to_string();
    }
    
    let count: int = m - n + 1;
    let total_sum: int = count * (n + m) / 2;
    let quotient: int = total_sum / count;
    let remainder: int = total_sum % count;
    
    let rounded = if remainder * 2 < count {
        quotient
    } else if remainder * 2 > count {
        quotient + 1
    } else if quotient % 2 == 0 {
        quotient
    } else {
        quotient + 1
    };
    
    proof {
        lemma_div_mod_range(total_sum, count);
        assert(0 <= remainder < count);
        lemma_rounding_condition(quotient, remainder, count);
    }
    
    let binary_rep = int_to_binary(int_to_nat(rounded));
    let mut result = String::from("0b");
    for i: nat in 0..binary_rep.len() {
        result.push(binary_rep[i]);
    }
    result
}
// </vc-code>


}

fn main() {}