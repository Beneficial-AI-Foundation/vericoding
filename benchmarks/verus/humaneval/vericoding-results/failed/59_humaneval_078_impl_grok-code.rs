// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_hex_char(c: char) -> bool {
    '0' <= c <= '9' || 'A' <= c <= 'F'
}

spec fn is_valid_hex_string(s: Seq<char>) -> bool {
    forall|i: int| #![auto] 0 <= i < s.len() ==> is_hex_char(s[i])
}

spec fn is_prime_hex_digit(c: char) -> bool {
    c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'
}

spec fn count_prime_hex_digits(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if is_prime_hex_digit(s[0]) { 1int } else { 0int }) + count_prime_hex_digits(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
exec fn count_prime_hex_digits_exec(s: &str) -> (ret: usize)
    requires
        is_valid_hex_string(s@),
    ensures
        ret as int == count_prime_hex_digits(s@),
        0 <= ret as int <= s@.len(),
    decreases s@.len()
{
/* helper modified by LLM (iteration 5): Fixed compilation error by using direct iteration over s.chars() instead of unsupported collect */
    let mut count = 0usize;
    for c in s.chars()
    {
        if is_prime_hex_digit(c) {
            count += 1;
        }
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn hex_key(num: &str) -> (count: usize)
    requires
        is_valid_hex_string(num@),
    ensures
        count as int >= 0,
        count as int <= num@.len(),
        count as int == count_prime_hex_digits(num@),
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Called the fixed helper function for counting */
    count_prime_hex_digits_exec(num)
}
// </vc-code>


}

fn main() {}