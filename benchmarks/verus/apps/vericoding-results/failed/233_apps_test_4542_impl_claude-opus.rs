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
proof fn lemma_count_segments_bounds(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        1 <= count_segments(s) <= s.len(),
    decreases s.len(),
{
    if s.len() <= 1 {
        assert(count_segments(s) == 1);
    } else {
        lemma_count_segments_bounds(s.subrange(0, s.len() - 1));
        assert(s.subrange(0, s.len() - 1).len() == s.len() - 1);
        assert(valid_input(s.subrange(0, s.len() - 1)));
        if s[s.len() - 1] != s[s.len() - 2] {
            assert(count_segments(s) == count_segments(s.subrange(0, s.len() - 1)) + 1);
        } else {
            assert(count_segments(s) == count_segments(s.subrange(0, s.len() - 1)));
        }
    }
}

/* helper modified by LLM (iteration 5): Fixed lemma to work with current index */
proof fn lemma_count_segments_step(s: Seq<char>, i: int)
    requires
        valid_input(s),
        0 < i <= s.len(),
    ensures
        i < s.len() ==> count_segments(s.subrange(0, i + 1)) == count_segments(s.subrange(0, i)) + if s[i] != s[i - 1] { 1int } else { 0int },
    decreases s.len() - i,
{
    if i < s.len() {
        let s_sub = s.subrange(0, i + 1);
        assert(s_sub.len() == i + 1);
        assert(s_sub[s_sub.len() - 1] == s[i]);
        assert(s_sub[s_sub.len() - 2] == s[i - 1]);
        assert(s_sub.subrange(0, s_sub.len() - 1) =~= s.subrange(0, i));
    }
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
    /* code modified by LLM (iteration 5): Fixed bounds checking and overflow issues */
    let n = s.len();
    assert(n > 0);
    
    proof {
        lemma_count_segments_bounds(s@);
    }
    
    if n == 1 {
        assert(count_segments(s@) == 1);
        return 0;
    }
    
    let mut segments: usize = 1;
    let mut i: usize = 1;
    
    assert(1 <= i && i <= n);
    assert(count_segments(s@.subrange(0, 1)) == 1);
    
    while i < n
        invariant
            1 <= i <= n,
            n == s.len(),
            valid_input(s@),
            1 <= segments <= i,
            segments as int == count_segments(s@.subrange(0, i as int)),
            segments as int <= s@.len(),
        decreases n - i,
    {
        assert(0 <= i - 1 < s.len());
        assert(0 <= i < s.len());
        
        if s[i] != s[i - 1] {
            segments = segments + 1;
        }
        
        proof {
            assert(0 < i as int < s@.len());
            lemma_count_segments_step(s@, i as int);
            assert(segments as int == count_segments(s@.subrange(0, i as int)) + if s@[i as int] != s@[i as int - 1] { 1int } else { 0int });
            assert(segments as int == count_segments(s@.subrange(0, (i + 1) as int)));
        }
        
        i = i + 1;
    }
    
    assert(i == n);
    assert(s@.subrange(0, n as int) =~= s@);
    assert(segments as int == count_segments(s@));
    
    let result = (segments - 1) as i8;
    proof {
        lemma_count_segments_bounds(s@);
        assert(1 <= count_segments(s@) <= s@.len());
        assert(0 <= segments - 1 < 128);
    }
    result
}
// </vc-code>


}

fn main() {}