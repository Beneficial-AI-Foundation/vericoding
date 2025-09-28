// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int) -> bool {
    1 <= r <= 100
}

spec fn dodecagon_area(r: int) -> int {
    3 * r * r
}

spec fn int_to_string(n: int) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string(n / 10) + int_to_string(n % 10)
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 1 {
        (s[0] as int) - ('0' as int)
    } else if s.len() > 1 {
        string_to_int(s.subrange(0, s.len() - 1)) * 10 + ((s[s.len() - 1] as int) - ('0' as int))
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): implement manual trim for &str to avoid unsupported std methods */
fn trim_str(input: &str) -> &str {
    let bytes = input.as_bytes();
    let mut start = 0i64;
    let mut end = input.len() as i64;
    while start < end && bytes[start as usize] == b' ' {
        start += 1;
    }
    while start < end && bytes[(end - 1) as usize] == b' ' {
        end -= 1;
    }
    &input[start as usize..end as usize]
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use manual trim helper and parse checked number */
{
    let s = trim_str(stdin_input);
    if let Ok(r) = s.parse::<i32>() {
        if r >= 1 && r <= 100 {
            let area = 3 * r * r;
            area.to_string()
        } else {
            "invalid".to_string()
        }
    } else {
        "invalid".to_string()
    }
}
// </vc-code>


}

fn main() {}