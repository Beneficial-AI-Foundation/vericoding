// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'B' || s[i] == 'W'
}

spec fn count_segments(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() <= 1 {
        1int
    } else {
        count_segments(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] != s[s.len() - 2] { 1int } else { 0int })
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_segments_tail(s: Seq<char>, idx: int) 
    requires 
        valid_input(s),
        0 <= idx < s.len(),
    ensures 
        count_segments(s) == count_segments(s.subrange(0, idx + 1)) + count_segments(s.subrange(idx + 1, s.len() as int)) - (if idx + 1 < s.len() && s[idx] == s[idx + 1] { 1int } else { 0int })
{
    /* helper modified by LLM (iteration 5): Fixed lemma with proper recursive proof */
    if s.len() <= 1 {
        assert(s.len() == 1);
        assert(idx == 0);
        assert(s.subrange(0, 1) == s);
        assert(s.subrange(1, 1).len() == 0);
        assert(count_segments(s.subrange(1, 1)) == 1);
    } else {
        if idx == s.len() - 1 {
            assert(s.subrange(0, s.len()) == s);
            assert(s.subrange(s.len(), s.len()).len() == 0);
            assert(count_segments(s.subrange(s.len(), s.len())) == 1);
        } else {
            lemma_count_segments_tail(s.subrange(0, s.len() - 1), idx);
            let last_char = s[s.len() - 1];
            let prev_char = s[s.len() - 2];
            assert(count_segments(s) == count_segments(s.subrange(0, s.len() - 1)) + (if last_char != prev_char { 1 } else { 0 }));
        }
    }
}

proof fn lemma_count_segments_append(s1: Seq<char>, s2: Seq<char>)
    requires
        valid_input(s1),
        valid_input(s2),
        s1.len() > 0,
        s2.len() > 0,
    ensures
        count_segments(s1 + s2) == 
            count_segments(s1) + count_segments(s2) -
            (if s1[s1.len() - 1] == s2[0] { 1int } else { 0int })
{
    /* helper modified by LLM (iteration 5): Complete recursive proof for append lemma */
    if s2.len() == 1 {
        if s1.len() == 1 {
            assert(count_segments(s1 + s2) == (if s1[0] == s2[0] { 1 } else { 2 }));
            assert(count_segments(s1) == 1);
            assert(count_segments(s2) == 1);
        } else {
            lemma_count_segments_append(s1.subrange(0, s1.len() - 1), s2);
            let last_char1 = s1[s1.len() - 1];
            let prev_char1 = s1[s1.len() - 2];
            assert(count_segments(s1) == count_segments(s1.subrange(0, s1.len() - 1)) + (if last_char1 != prev_char1 { 1 } else { 0 }));
            assert(count_segments(s1 + s2) == count_segments(s1.subrange(0, s1.len() - 1) + s2) + (if last_char1 != s2[0] { 1 } else { 0 }));
        }
    } else {
        lemma_count_segments_append(s1, s2.subrange(0, s2.len() - 1));
        let last_char2 = s2[s2.len() - 1];
        let prev_char2 = s2[s2.len() - 2];
        assert(count_segments(s2) == count_segments(s2.subrange(0, s2.len() - 1)) + (if last_char2 != prev_char2 { 1 } else { 0 }));
        assert(count_segments(s1 + s2) == count_segments(s1 + s2.subrange(0, s2.len() - 1)) + (if last_char2 != (s1 + s2.subrange(0, s2.len() - 1))[(s1.len() + s2.len() - 2)] { 1 } else { 0 }));
        assert((s1 + s2.subrange(0, s2.len() - 1))[(s1.len() + s2.len() - 2)] == s2[s2.len() - 2]);
    }
}

fn count_segments_iter(s: &Vec<char>) -> (count: u32)
    requires
        valid_input(s@),
    ensures
        count as int == count_segments(s@),
        count >= 1,
{
    /* helper modified by LLM (iteration 5): Fixed loop invariant and arithmetic */
    let mut i = 0;
    let mut seg_count = 1u32;
    
    while i < s.len() - 1
        invariant
            0 <= i <= s.len() - 1,
            seg_count >= 1,
            seg_count <= i + 1,
            seg_count as int == count_segments(s@.subrange(0, i + 1)),
        decreases
            s.len() - i - 1,
    {
        assert(i + 1 < s.len());
        if s[i] != s[i + 1] {
            seg_count = seg_count + 1;
        }
        i = i + 1;
        assert(seg_count as int == count_segments(s@.subrange(0, i)));
    }
    
    seg_count
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires 
        valid_input(s@),
    ensures 
        result >= 0,
        result as int == count_segments(s@) - 1,
        result as int <= s.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed casting and arithmetic */
    let total_segments = count_segments_iter(&s);
    assert(total_segments as int == count_segments(s@));
    assert(total_segments >= 1);
    let result = if total_segments > 0 { (total_segments - 1) as i8 } else { 0i8 };
    assert(result >= 0);
    assert(result as int == count_segments(s@) - 1);
    assert(result as int <= s.len() as int - 1);
    result
}
// </vc-code>


}

fn main() {}