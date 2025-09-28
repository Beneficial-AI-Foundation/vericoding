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
/* helper modified by LLM (iteration 5): fixed type mismatch by casting s.len() to usize */
fn count_prime_hex_digits_lemma(s: Seq<char>, i: usize)
    requires
        i <= s.len(),
    ensures
        count_prime_hex_digits(s.subrange(i as int, s.len() as int)) >= 0,
        count_prime_hex_digits(s.subrange(i as int, s.len() as int)) <= s.len() - i as int,
    decreases s.len() - i as int
{
    if i == s.len() as usize {
        assert(s.subrange(i as int, s.len() as int) == Seq::<char>::empty());
    } else {
        count_prime_hex_digits_lemma(s, i + 1);
    }
}

fn count_prime_hex_digits_step(s: Seq<char>, i: usize)
    requires
        i < s.len(),
    ensures
        count_prime_hex_digits(s.subrange(i as int, s.len() as int)) == 
            (if is_prime_hex_digit(s[i as int]) { 1int } else { 0int }) + 
            count_prime_hex_digits(s.subrange((i + 1) as int, s.len() as int)),
{
    assert(s.subrange(i as int, s.len() as int)[0] == s[i as int]);
    assert(s.subrange(i as int, s.len() as int).subrange(1, (s.len() - i as int) as int) == s.subrange((i + 1) as int, s.len() as int));
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
    /* code modified by LLM (iteration 5): fixed type compatibility by using proper usize types */
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < num.len()
        invariant
            i <= num.len(),
            count as int == count_prime_hex_digits(num@.subrange(0, i as int)),
            count <= i,
        decreases num.len() - i
    {
        proof {
            count_prime_hex_digits_step(num@, i);
        }
        
        let c = num.chars().nth(i).unwrap();
        
        if is_prime_hex_digit(c) {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(num@.subrange(0, num@.len() as int) == num@);
    }
    
    count
}
// </vc-code>


}

fn main() {}