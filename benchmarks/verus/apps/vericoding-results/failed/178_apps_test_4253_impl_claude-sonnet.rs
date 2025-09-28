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
/* helper modified by LLM (iteration 5): implement string parsing without as_bytes() using char iteration */
exec fn parse_string_to_u32(s: &str) -> u32
{
    let mut result: u32 = 0;
    let chars = s.chars();
    
    for c in chars {
        if c.is_ascii_digit() {
            let digit = (c as u32) - ('0' as u32);
            result = result * 10 + digit;
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use char-based parsing helper */
    let r_str = stdin_input.trim();
    let r = parse_string_to_u32(r_str);
    
    let area = 3 * r * r;
    area.to_string()
}
// </vc-code>


}

fn main() {}