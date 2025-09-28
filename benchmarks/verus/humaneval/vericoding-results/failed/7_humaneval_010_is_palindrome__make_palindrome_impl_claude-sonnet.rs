// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_palindrome(s: Seq<char>) -> bool {
    forall|k: int| #![trigger s.index(k)] 0 <= k < s.len() ==> s.index(k) == s.index(s.len() - 1 - k)
}

spec fn starts_with(result: Seq<char>, s: Seq<char>) -> bool {
    result.len() >= s.len() && forall|k: int| #![trigger result.index(k)] 0 <= k < s.len() ==> result.index(k) == s.index(k)
}
// </vc-preamble>

// <vc-helpers>
spec fn is_suffix_of_reverse(s: Seq<char>, suffix: Seq<char>) -> bool {
    suffix.len() <= s.len() && forall|k: int| #![trigger suffix.index(k)] 0 <= k < suffix.len() ==> suffix.index(k) == s.index(s.len() - 1 - k)
}

/* helper modified by LLM (iteration 5): use add method for sequence concatenation */
fn lemma_palindrome_construction(s: Seq<char>, prefix: Seq<char>)
    requires
        is_suffix_of_reverse(s, prefix),
    ensures
        is_palindrome(prefix.add(s)),
        starts_with(prefix.add(s), s)
{
    let result = prefix.add(s);
    assert forall|k: int| 0 <= k < result.len() implies result.index(k) == result.index(result.len() - 1 - k) by {
        if k < s.len() {
            assert(result.index(k) == s.index(k));
            assert(result.index(result.len() - 1 - k) == prefix.index(prefix.len() - 1 - (k)));
            assert(prefix.index(prefix.len() - 1 - k) == s.index(s.len() - 1 - k));
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn make_palindrome(s: &str) -> (result: String)
    ensures 
        result@.len() <= 2 * s@.len(),
        is_palindrome(result@),
        starts_with(result@, s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use indexed string access instead of chars().collect() */
    let s_seq = s@;
    let mut prefix: Vec<char> = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            prefix.len() == i,
            forall|k: int| 0 <= k < i ==> prefix@.index(k) == s_seq.index(s_seq.len() - 1 - k),
        decreases s.len() - i
    {
        let char_at_end = s.get_char((s.len() - 1 - i) as usize);
        prefix.push(char_at_end);
        i += 1;
    }
    
    proof {
        assert(is_suffix_of_reverse(s_seq, prefix@));
        lemma_palindrome_construction(s_seq, prefix@);
    }
    
    let mut result = String::new();
    for c in prefix.iter() {
        result.push(*c);
    }
    result.push_str(s);
    
    result
}
// </vc-code>


}

fn main() {}