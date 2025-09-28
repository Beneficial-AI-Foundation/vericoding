use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

// <vc-helpers>
// Helper lemma to prove properties about filter length
proof fn lemma_filter_len_bounded<T>(s: Seq<T>, f: spec_fn(T) -> bool)
    ensures s.filter(f).len() <= s.len()
{
    if s.len() == 0 {
    } else {
        lemma_filter_len_bounded(s.drop_first(), f);
    }
}

// Helper lemma about filter and subrange
proof fn lemma_filter_subrange(s: Seq<char>, i: int, f: spec_fn(char) -> bool)
    requires 0 <= i <= s.len()
    ensures s.subrange(0, i).filter(f).len() <= s.filter(f).len()
{
    if i == 0 {
    } else if i == s.len() {
        assert(s.subrange(0, i) =~= s);
    } else {
        lemma_filter_subrange(s, i - 1, f);
    }
}

// Helper function to get character at index
spec fn char_at(s: &str, i: int) -> char
    recommends 0 <= i < s@.len()
{
    s@[i]
}

// Helper function that's an exec version of is_upper_case
fn is_upper_case_exec(c: char) -> (result: bool)
    ensures result == is_upper_case(c)
{
    65 <= c as u32 && c as u32 <= 90
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
            count as int == s@.subrange(0, i as int).filter(|c: char| is_upper_case(c)).len(),
    {
        let c = s.get_char(i);
        if is_upper_case_exec(c) {
            count = count + 1;
        }
        
        proof {
            let old_i = i as int;
            let new_i = (i + 1) as int;
            
            assert(s@.subrange(0, new_i) =~= s@.subrange(0, old_i).push(s@[old_i]));
            
            if is_upper_case(c) {
                assert(s@.subrange(0, new_i).filter(|c: char| is_upper_case(c)) =~= 
                       s@.subrange(0, old_i).filter(|c: char| is_upper_case(c)).push(c));
            } else {
                assert(s@.subrange(0, new_i).filter(|c: char| is_upper_case(c)) =~= 
                       s@.subrange(0, old_i).filter(|c: char| is_upper_case(c)));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
        lemma_filter_len_bounded(s@, |c: char| is_upper_case(c));
    }
    
    count
}
// </vc-code>

fn main() {}

}