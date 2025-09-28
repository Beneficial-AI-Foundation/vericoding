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
    /* code modified by LLM (iteration 5): fixed invalid suffixes by removing 'int' from number literals */
    if n > m {
        "-1".to_string()
    } else {
        let count = m - n + 1;
        let total_sum = count * (n + m) / 2;
        let quotient = total_sum / count;
        let remainder = total_sum % count;
        let rounded = if remainder * 2 < count {
            quotient
        } else if remainder * 2 > count {
            quotient + 1
        } else {
            if quotient % 2 == 0 {
                quotient
            } else {
                quotient + 1
            }
        };
        proof {
            assert(rounded >= 0);
        }
        let mut r = rounded;
        let mut bin_parts: Vec<char> = Vec::new();
        if r == 0 {
            bin_parts.push('0');
        } else {
            while r > 0
                invariant r >= 0
            {
                bin_parts.push(if r % 2 == 1 { '1' } else { '0' });
                r = r / 2;
            }
            bin_parts.reverse();
        }
        let mut result = String::new();
        result.push('0');
        result.push('b');
        for c in bin_parts {
            result.push(c);
        }
        result
    }
}
// </vc-code>


}

fn main() {}