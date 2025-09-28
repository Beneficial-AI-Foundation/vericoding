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
proof fn lemma_count_prime_digits_concat(s1: Seq<char>, s2: Seq<char>)
    ensures
        count_prime_hex_digits(s1 + s2) == count_prime_hex_digits(s1) + count_prime_hex_digits(s2),
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_count_prime_digits_concat(s1.subrange(1, s1.len() as int), s2);
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
    let mut count: usize = 0;
    let mut i: usize = 0;
    let bytes = num.as_bytes();

    while i < num.len()
        invariant
            0 <= i <= num.len(),
            is_valid_hex_string(num@),
            count as int == count_prime_hex_digits(num@.subrange(0, i as int)),
        decreases num.len() - i
    {
        let c = bytes[i] as char;

        proof {
            lemma_count_prime_digits_concat(num@.subrange(0, i as int), seq![num@[i as int]]);
        }

        if c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D' {
            count = count + 1;
        }

        i = i + 1;
    }

    count
}
// </vc-code>


}

fn main() {}