// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 4 && forall|i: int| 0 <= i < s.len() ==> s[i] == '+' || s[i] == '-'
}

spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0nat as int
    } else {
        (if s[0] == c { 1nat as int } else { 0nat as int }) + count_char(s.subrange(1, s.len() as int), c)
    }
}

spec fn calculate_sum(s: Seq<char>) -> int {
    count_char(s, '+') - count_char(s, '-')
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing exclamation marks */
lemma count_char_range_property(s: Seq<char>, c: char, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        count_char(s.subrange(start, end), c) >= 0,
    decreases end - start
{
    if start == end {
        assert(s.subrange(start, end).len() == 0);
    } else {
        count_char_range_property(s, c, start + 1, end);
    }
}

lemma count_char_accumulate(s: Seq<char>, c: char, i: int)
    requires
        0 <= i < s.len(),
    ensures
        count_char(s, c) == count_char(s.subrange(0, i), c) + (if s[i] == c { 1 } else { 0 }) + count_char(s.subrange(i + 1, s.len() as int), c),
{
    if i == 0 {
        assert(s.subrange(0, 0).len() == 0);
        assert(count_char(s.subrange(0, 0), c) == 0);
        assert(s.subrange(1, s.len() as int) == s.subrange(1, s.len() as int));
    } else {
        count_char_accumulate(s.subrange(1, s.len() as int), c, i - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == calculate_sum(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementation using lemmas without exclamation marks */
    let mut plus_count: i8 = 0;
    let mut minus_count: i8 = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == 4,
            plus_count as int == count_char(s@.subrange(0, i as int), '+'),
            minus_count as int == count_char(s@.subrange(0, i as int), '-'),
            plus_count >= 0,
            minus_count >= 0,
            plus_count <= 4,
            minus_count <= 4,
        decreases s.len() - i
    {
        proof {
            count_char_range_property(s@, '+', 0, i as int);
            count_char_range_property(s@, '-', 0, i as int);
        }
        
        if s[i] == '+' {
            plus_count = plus_count + 1;
        } else {
            minus_count = minus_count + 1;
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == s.len());
        assert(s@.subrange(0, i as int) == s@);
    }
    
    plus_count - minus_count
}
// </vc-code>


}

fn main() {}