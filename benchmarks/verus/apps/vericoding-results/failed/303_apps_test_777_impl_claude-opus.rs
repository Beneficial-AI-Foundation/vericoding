// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && s.len() <= 20 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 'a' && #[trigger] s[i] <= 'z'
}

spec fn distinct_strings_count(s: Seq<char>) -> int
    recommends valid_input(s)
{
    s.len() as int * 25 + 26
}

spec fn int_to_string_spec(n: int) -> Seq<char>
    recommends n >= 0
{
    if n == 0 { seq!['0'] }
    else { seq!['0'] } // Simplified for termination
}

spec fn char_of_digit_spec(d: int) -> char
    recommends 0 <= d <= 9
{
    if d == 0 { '0' }
    else if d == 1 { '1' }
    else if d == 2 { '2' }
    else if d == 3 { '3' }
    else if d == 4 { '4' }
    else if d == 5 { '5' }
    else if d == 6 { '6' }
    else if d == 7 { '7' }
    else if d == 8 { '8' }
    else if d == 9 { '9' }
    else { '0' }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add char_of_digit exec function for runtime conversion */
fn char_of_digit(d: u32) -> (c: char)
    requires 0 <= d <= 9
    ensures c == char_of_digit_spec(d as int)
{
    if d == 0 { '0' }
    else if d == 1 { '1' }
    else if d == 2 { '2' }
    else if d == 3 { '3' }
    else if d == 4 { '4' }
    else if d == 5 { '5' }
    else if d == 6 { '6' }
    else if d == 7 { '7' }
    else if d == 8 { '8' }
    else { '9' }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: &str) -> (result: String)
    requires valid_input(s@)
    ensures result@ == int_to_string_spec(distinct_strings_count(s@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use format! macro for string construction */
    let count: u32 = (s.unicode_len() * 25 + 26) as u32;
    
    // Convert count to string
    if count == 0 {
        "0".to_string()
    } else {
        // For simplicity, we'll handle the specific range we know
        // Since s.unicode_len() is between 1 and 20, count is between 51 and 526
        if count < 100 {
            // Two digits
            let tens = count / 10;
            let ones = count % 10;
            let c1 = char_of_digit(tens);
            let c2 = char_of_digit(ones);
            format!("{}{}", c1, c2)
        } else {
            // Three digits
            let hundreds = count / 100;
            let tens = (count % 100) / 10;
            let ones = count % 10;
            let c1 = char_of_digit(hundreds);
            let c2 = char_of_digit(tens);
            let c3 = char_of_digit(ones);
            format!("{}{}{}", c1, c2, c3)
        }
    }
}
// </vc-code>


}

fn main() {}