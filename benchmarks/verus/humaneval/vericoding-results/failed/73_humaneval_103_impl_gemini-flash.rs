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
    /* code modified by LLM (iteration 2): convert rounded to `nat` type only when passing to spec function */
    if n > m {
        return "-1".to_string();
    }

    let count: int = m - n + 1;
    let total_sum: int = count * (n + m) / 2;
    let quotient: int = total_sum / count;
    let remainder: int = total_sum % count;

    let rounded_val: int;
    if remainder * 2 < count {
        rounded_val = quotient;
    } else if remainder * 2 > count {
        rounded_val = quotient + 1;
    } else {
        if quotient % 2 == 0 {
            rounded_val = quotient;
        } else {
            rounded_val = quotient + 1;
        }
    }

    // Prove that rounded_val is non-negative before casting to nat
    // These assertions are for verifier, not runtime
    proof {
        assert(n > 0 && m > 0) by {}; // from requires clause
        assert(n <= m) by {}; // conditioned on this branch
        assert(count >= 1) by {}; // m - n + 1 >= 1
        assert(n + m >= 2) by {}; // since n >= 1 and m >= 1
        assert(total_sum == count * (n + m) / 2);
        assert(total_sum >= 0) by {}; // count >= 1 and (n+m) >= 2
        assert(quotient >= 0) by {}; // total_sum >= 0 and count >= 1
        assert(remainder >= 0 && remainder < count) by {}; // definition of % operator in Verus for positive operands
        assert(rounded_val >= 0) by {};
    }
    
    // Cast to nat only when calling the spec function
    let binary_seq = int_to_binary(rounded_val as nat);

    let mut binary_string = String::new();
    binary_string.push_str("0b");
    for char_val in binary_seq.iter() {
        binary_string.push(*char_val);
    }

    binary_string
}
// </vc-code>


}

fn main() {}