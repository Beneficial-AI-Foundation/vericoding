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
/* helper modified by LLM (iteration 5): fixed ensures clause syntax by removing trailing comma */
fn nat_to_binary_string(n: nat) -> (s: String)
    decreases n
    ensures s@ == int_to_binary(n)
{
    if n == 0 {
        "0".to_string()
    } else if n <= 1 {
        "1".to_string()
    } else {
        let rest = nat_to_binary_string(n / 2);
        let bit = if n % 2 == 1 { "1" } else { "0" };
        rest + bit
    }
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
/* code modified by LLM (iteration 5): unchanged from iteration 4 */
{
    if n > m {
        "-1".to_string()
    } else {
        let count: nat = (m - n + 1) as nat;
        let total_sum: int = (count as int) * (n + m) / 2;
        let quotient = total_sum / (count as int);
        let remainder = total_sum % (count as int);
        let rounded: int = 
            if remainder * 2 < (count as int) {
                quotient
            } else if remainder * 2 > (count as int) {
                quotient + 1
            } else {
                if quotient % 2 == 0 {
                    quotient
                } else {
                    quotient + 1
                }
            };
        let binary_str = nat_to_binary_string(rounded as nat);
        "0b".to_string() + &binary_str
    }
}
// </vc-code>


}

fn main() {}