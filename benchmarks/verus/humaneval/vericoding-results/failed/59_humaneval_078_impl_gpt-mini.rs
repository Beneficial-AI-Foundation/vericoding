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
/* helper modified by LLM (iteration 5): prove 0 <= count_prime_hex_digits(s) <= s.len() */
proof fn count_prime_hex_digits_bounds(s: Seq<char>)
    ensures
        0 <= count_prime_hex_digits(s),
        count_prime_hex_digits(s) <= s.len() as int,
    decreases s.len()
{
    if s.len() == 0 {
        assert(count_prime_hex_digits(s) == 0);
    } else {
        count_prime_hex_digits_bounds(s.subrange(1, s.len() as int));
        proof {
            let tail = count_prime_hex_digits(s.subrange(1, s.len() as int));
            if is_prime_hex_digit(s[0]) {
                assert(count_prime_hex_digits(s) == 1int + tail);
                assert(0 <= 1int + tail);
                assert(1int + tail <= s.len() as int);
            } else {
                assert(count_prime_hex_digits(s) == tail);
                assert(0 <= tail);
                assert(tail <= s.len() as int - 1int);
                assert(tail <= s.len() as int);
            }
        }
    }
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
    /* code modified by LLM (iteration 5): compute ghost count and cast to usize */
    let c_ghost: tracked int = count_prime_hex_digits(num@);
    proof {
        count_prime_hex_digits_bounds(num@);
    }
    let count: usize = c_ghost as usize;
    count
}

// </vc-code>


}

fn main() {}