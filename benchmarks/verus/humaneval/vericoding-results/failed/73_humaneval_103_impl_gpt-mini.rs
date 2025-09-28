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
/* helper modified by LLM (iteration 5): compute count and total sum for range */
fn compute_count_and_sum(n: int, m: int) -> (int, int)
    requires n > 0 && m > 0 && n <= m,
    ensures
        result.0 == m - n + 1,
        result.1 == result.0 * (n + m) / 2,
{
    let c = m - n + 1;
    let s = c * (n + m) / 2;
    (c, s)
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
    /* code modified by LLM (iteration 5): implement rounded_avg including rounding and binary conversion */
    if n > m {
        "-1".to_string()
    } else {
        let (count, total_sum) = compute_count_and_sum(n, m);
        let quotient = total_sum / count;
        let remainder = total_sum % count;
        let rounded = if remainder * 2 < count { quotient }
                      else if remainder * 2 > count { quotient + 1 }
                      else if quotient % 2 == 0 { quotient }
                      else { quotient + 1 };
        let mut s = "0b".to_string();
        if rounded == 0 {
            s.push('0');
        } else {
            let mut val: nat = rounded as nat;
            let mut rev: Vec<char> = Vec::new();
            while val > 0
                invariant
                    val >= 0,
                decreases val
            {
                let bit = if val % 2 == 1 { '1' } else { '0' };
                rev.push(bit);
                val = val / 2;
            }
            let mut i: usize = 0;
            let len = rev.len();
            while i < len
                invariant
                    i <= len,
                decreases len - i
            {
                s.push(rev[len - 1 - i]);
                i = i + 1;
            }
        }
        proof {
            assert(n <= m);
            assert(count == m - n + 1);
            assert(total_sum == count * (n + m) / 2);
            assert(quotient == total_sum / count);
            assert(remainder == total_sum % count);
            assert(rounded == if remainder * 2 < count { quotient }
                              else if remainder * 2 > count { quotient + 1 }
                              else if quotient % 2 == 0 { quotient }
                              else { quotient + 1 });
            assert(s@ == seq!['0','b'] + int_to_binary(rounded as nat));
        }
        s
    }
}

// </vc-code>


}

fn main() {}