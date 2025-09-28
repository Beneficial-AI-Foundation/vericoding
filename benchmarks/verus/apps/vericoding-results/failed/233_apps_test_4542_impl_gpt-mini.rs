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
/* helper modified by LLM (iteration 5): lemma relating count_segments when extending sequence by one element */
fn count_segments_extend(s: Seq<char>, i: int)
    requires
        1 <= i,
        i < s.len(),
    ensures
        count_segments(s.subrange(0, i+1)) == count_segments(s.subrange(0, i)) + (if s[i] != s[i-1] { 1int } else { 0int }),
    decreases
        s.len() - i
{
    proof {
        assert(count_segments(s.subrange(0, i+1)) ==
            if s.subrange(0, i+1).len() <= 1 {
                1int
            } else {
                count_segments(s.subrange(0, i+1).subrange(0, s.subrange(0, i+1).len() - 1)) + (if s.subrange(0, i+1)[s.subrange(0, i+1).len() - 1] != s.subrange(0, i+1)[s.subrange(0, i+1).len() - 2] { 1int } else { 0int })
            });
        // Since i >= 1, the prefix of length i+1 has length >= 2, so simplify
        assert(s.subrange(0, i+1).subrange(0, s.subrange(0, i+1).len() - 1) == s.subrange(0, i));
        assert(s.subrange(0, i+1)[s.subrange(0, i+1).len() - 1] == s[i]);
        assert(s.subrange(0, i+1)[s.subrange(0, i+1).len() - 2] == s[i-1]);
        assert(count_segments(s.subrange(0, i+1)) == count_segments(s.subrange(0, i)) + (if s[i] != s[i-1] { 1int } else { 0int }));
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
/* code modified by LLM (iteration 5): runtime loop over Vec with ghost invariants and proof */
{
    let n: usize = s.len();
    let mut i: usize = 1usize;
    let mut t: i8 = 0i8;
    while i < n
        invariant
            1 <= i as int <= s@.len(),
            0 <= t as int <= s@.len() - 1,
            t as int == count_segments(s@.subrange(0, i as int)) - 1,
        decreases
            s@.len() - i as int
    {
        let old_i = i;
        let old_t = t;
        if s[old_i] != s[old_i - 1] {
            t = old_t + 1i8;
        } else {
            t = old_t;
        }
        i = old_i + 1;
        proof {
            count_segments_extend(s@, old_i as int);
            assert(count_segments(s@.subrange(0, (old_i + 1) as int)) == count_segments(s@.subrange(0, old_i as int)) + (if s@[(old_i as int)] != s@[((old_i as int) - 1)] { 1int } else { 0int }));
            assert(old_t as int == count_segments(s@.subrange(0, old_i as int)) - 1);
            assert(t as int == count_segments(s@.subrange(0, (old_i + 1) as int)) - 1);
        }
    }
    let result: i8 = t;
    result
}

// </vc-code>


}

fn main() {}