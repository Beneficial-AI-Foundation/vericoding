use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// <vc-helpers>
// Helper function that can be executed at runtime
fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    65 <= c as u32 && c as u32 <= 90
}

// Helper lemma to establish the relationship between the count at each step
proof fn count_uppercase_invariant(s: Seq<char>, i: int, count: int)
    requires
        0 <= i <= s.len(),
        count >= 0,
        count == s.subrange(0, i).filter(|c: char| is_upper_case(c)).len(),
    ensures
        count <= i,
{
    // The filtered sequence length is at most the original sequence length
    assert(s.subrange(0, i).filter(|c: char| is_upper_case(c)).len() <= s.subrange(0, i).len());
    assert(s.subrange(0, i).len() == i);
}

// Lemma to prove that extending the range by one element updates the filter correctly
proof fn filter_extend_lemma(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.subrange(0, i + 1).filter(|c: char| is_upper_case(c)) ==
        if is_upper_case(s[i]) {
            s.subrange(0, i).filter(|c: char| is_upper_case(c)).push(s[i])
        } else {
            s.subrange(0, i).filter(|c: char| is_upper_case(c))
        },
{
    assert(s.subrange(0, i + 1) == s.subrange(0, i).push(s[i]));
}
// </vc-helpers>

// <vc-spec>
fn count_uppercase(s: &str) -> (count: usize)
    ensures 
        count >= 0,
        count as int == s@.filter(|c: char| is_upper_case(c)).len(),
// </vc-spec>
// <vc-code>
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    let len = s.unicode_len();
    
    while i < len
        invariant
            0 <= i <= len,
            len == s@.len(),
            count >= 0,
            count as int == s@.subrange(0, i as int).filter(|c: char| is_upper_case(c)).len(),
    {
        let c = s.get_char(i);
        
        proof {
            filter_extend_lemma(s@, i as int);
        }
        
        if is_upper_case_exec(c) {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, len as int) == s@.subrange(0, s@.len() as int));
        assert(s@.subrange(0, s@.len() as int) == s@);
    }
    
    count
}
// </vc-code>

fn main() {}

}