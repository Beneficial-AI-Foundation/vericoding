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

// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): parse number directly from string without using as_bytes() */
    let input_str = stdin_input;
    let mut r: u32 = 0;
    let mut started = false;
    
    let input_len = input_str.len();
    let mut i: usize = 0;
    
    while i < input_len
        invariant
            i <= input_len,
    {
        let ch_opt = input_str.chars().nth(i);
        if ch_opt.is_some() {
            let ch = ch_opt.unwrap();
            if ch >= '0' && ch <= '9' {
                started = true;
                let digit = (ch as u32) - ('0' as u32);
                r = r * 10 + digit;
            } else if started {
                break;
            }
        }
        i = i + 1;
    }
    
    // Calculate the area
    let area = 3 * r * r;
    
    // Convert to string and return
    let output = area.to_string();
    output
}
// </vc-code>


}

fn main() {}