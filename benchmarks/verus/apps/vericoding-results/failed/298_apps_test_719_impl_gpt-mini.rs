// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn int_to_string(n: int) -> Seq<char> {
    unimplemented!()
}

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0 &&
    exists|k: int| k >= 1 && k <= 10000 && stdin_input == int_to_string(k).push('\n')
}

spec fn kth_perfect_number(k: int) -> int
    recommends k >= 1 && k <= 10000
{
    if k == 1 { 19 }
    else if k == 2 { 28 }
    else if k == 3 { 37 }
    else if k == 4 { 46 }
    else if k == 5 { 55 }
    else if k == 6 { 64 }
    else if k == 7 { 73 }
    else if k == 8 { 82 }
    else if k == 9 { 91 }
    else if k == 10 { 109 }
    else { 10 * (k - 9) + 99 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute kth perfect number using i64 */
fn compute_kth_perfect_number_exec(k: i64) -> (result: i64)
    requires k >= 1_i64 && k <= 10000_i64,
    ensures result == if k == 1_i64 { 19_i64 } else if k == 2_i64 { 28_i64 } else if k == 3_i64 { 37_i64 } else if k == 4_i64 { 46_i64 } else if k == 5_i64 { 55_i64 } else if k == 6_i64 { 64_i64 } else if k == 7_i64 { 73_i64 } else if k == 8_i64 { 82_i64 } else if k == 9_i64 { 91_i64 } else if k == 10_i64 { 109_i64 } else { 10_i64 * (k - 9_i64) + 99_i64 },
{
    let result = if k == 1_i64 { 19_i64 }
    else if k == 2_i64 { 28_i64 }
    else if k == 3_i64 { 37_i64 }
    else if k == 4_i64 { 46_i64 }
    else if k == 5_i64 { 55_i64 }
    else if k == 6_i64 { 64_i64 }
    else if k == 7_i64 { 73_i64 }
    else if k == 8_i64 { 82_i64 }
    else if k == 9_i64 { 91_i64 }
    else if k == 10_i64 { 109_i64 }
    else { 10_i64 * (k - 9_i64) + 99_i64 };
    result
}

/* helper modified by LLM (iteration 5): convert non-negative i64 to decimal String */
fn int_to_decimal_string(mut n: i64) -> (result: String)
    requires n >= 0_i64,
    ensures result@.len() > 0,
{
    let mut s: String = String::new();
    if n == 0_i64 {
        s.push('0');
        let result = s;
        result
    } else {
        let mut rev: Vec<char> = Vec::new();
        while n > 0_i64
            invariant
                n >= 0_i64,
            decreases n
        {
            let d = (n % 10_i64) as u8;
            let c = (48u8 + d) as char;
            rev.push(c);
            n = n / 10_i64;
        }
        let mut j: usize = 0usize;
        while j < rev.len()
            invariant
                j <= rev.len(),
            decreases rev.len() - j
        {
            s.push(rev[rev.len() - 1 - j]);
            j += 1;
        }
        let result = s;
        result
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: String) -> (result: String)
    requires valid_input(stdin_input@)
    ensures (exists|k: int| k >= 1 && k <= 10000 && 
        stdin_input@ == int_to_string(k).push('\n') &&
        result@ == int_to_string(kth_perfect_number(k)).push('\n')) &&
        result@.len() > 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): parse input to i64, compute perfect, convert to string and return */
{
    let bytes: Vec<u8> = stdin_input.into_bytes();
    let mut i: usize = 0usize;
    let mut k: i64 = 0_i64;

    while i < bytes.len() && bytes[i] != b'\n'
        invariant
            k >= 0_i64,
            i <= bytes.len(),
        decreases bytes.len() - i
    {
        let digit = (bytes[i] - b'0') as i64;
        k = k * 10_i64 + digit;
        i += 1;
    }

    let n = compute_kth_perfect_number_exec(k);
    let mut result: String = int_to_decimal_string(n);
    result.push('\n');
    result
}

// </vc-code>


}

fn main() {}