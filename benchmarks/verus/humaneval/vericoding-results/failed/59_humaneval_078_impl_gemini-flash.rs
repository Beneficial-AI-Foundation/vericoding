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
/* helper modified by LLM (iteration 5): The previous helper section was empty, so it was removed */
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
/* code modified by LLM (iteration 5): Cast `i` to `int` for comparison with `s_seq.len()` to resolve type mismatch. */
{
    let s_seq = num@;
    let mut count: usize = 0;
    let mut i: usize = 0;

    while i < s_seq.len()
        invariant
            0 <= i && i as nat <= s_seq.len(),
            count as int == count_prime_hex_digits(s_seq.subrange(0, i as int)),
    {
        let char_at_i = num.as_bytes()[i] as char;

        if is_prime_hex_digit(char_at_i) {
            count = count + 1;
        }
        i = i + 1;
    }

    count
}
// </vc-code>


}

fn main() {}