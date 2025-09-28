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

proof fn lemma_count_prime_hex_digits_base()
    ensures
        count_prime_hex_digits(Seq::empty()) == 0,
{
}

proof fn lemma_count_prime_hex_digits_rec(s: Seq<char>)
    requires
        s.len() > 0,
    ensures
        count_prime_hex_digits(s) == (if is_prime_hex_digit(s[0]) { 1int } else { 0int }) + count_prime_hex_digits(s.subrange(1, s.len() as int)),
{
}

spec fn is_prime_hex_digit_char(c: char) -> bool {
    c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'
}

/* helper modified by LLM (iteration 5): change access pattern to use chars() iterator */

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
    /* code modified by LLM (iteration 5): use chars() iterator instead of char_at */
    let mut count: usize = 0;
    let s = num.chars().collect::<Vec<char>>();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s@.len(),
            count >= 0,
            count <= i,
            count as int == count_prime_hex_digits(s@.subrange(0, i as int)),
        decreases s@.len() - i,
    {
        let c = s[i];
        
        if is_prime_hex_digit_char(c) {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}