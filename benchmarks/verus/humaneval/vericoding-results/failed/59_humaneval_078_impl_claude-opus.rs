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
/* helper modified by LLM (iteration 5): Fixed type annotations for integer literals */
proof fn lemma_count_prime_hex_digits_subrange(s: Seq<char>, k: int)
    requires
        0 <= k <= s.len(),
        is_valid_hex_string(s),
    ensures
        count_prime_hex_digits(s.subrange(0, k)) == 
            if k == 0 { 0int } 
            else { count_prime_hex_digits(s.subrange(0, k - 1)) + 
                   (if is_prime_hex_digit(s[k - 1]) { 1int } else { 0int }) },
{
    if k == 0 {
        assert(s.subrange(0, 0).len() == 0);
    } else {
        assert(s.subrange(0, k) =~= s.subrange(0, k - 1).push(s[k - 1]));
    }
}

proof fn lemma_count_prime_hex_digits_bounds(s: Seq<char>)
    requires
        is_valid_hex_string(s),
    ensures
        0 <= count_prime_hex_digits(s) <= s.len(),
        s.subrange(0, s.len() as int) =~= s,
{
    // Proof by induction on sequence length
    if s.len() == 0 {
        assert(count_prime_hex_digits(s) == 0);
    } else {
        lemma_count_prime_hex_digits_bounds(s.subrange(1, s.len() as int));
        assert(count_prime_hex_digits(s) <= s.len());
    }
    assert(s.subrange(0, s.len() as int) =~= s);
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
    /* code modified by LLM (iteration 5): Fixed decreases clause to use num@.len() instead of num.unicode_len() */
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < num.unicode_len()
        invariant
            0 <= i <= num@.len(),
            0 <= count <= i,
            count as int == count_prime_hex_digits(num@.subrange(0, i as int)),
            is_valid_hex_string(num@),
        decreases num@.len() - i as int
    {
        let c = num.get_char(i);
        if c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D' {
            count = count + 1;
        }
        
        proof {
            lemma_count_prime_hex_digits_subrange(num@, (i + 1) as int);
            assert(num@.subrange(0, (i + 1) as int) =~= num@.subrange(0, i as int).push(num@[i as int]));
        }
        
        i = i + 1;
    }
    
    proof {
        lemma_count_prime_hex_digits_bounds(num@);
        assert(num@.subrange(0, num@.len() as int) =~= num@);
    }
    
    count
}
// </vc-code>


}

fn main() {}