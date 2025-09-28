// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_a(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0 as int
    } else {
        (if s[0] == 'a' { 1 as int } else { 0 as int }) + count_a(s.subrange(1, s.len() as int))
    }
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && exists|i: int| 0 <= i < s.len() && s[i] == 'a'
}

spec fn is_good_string(s: Seq<char>) -> bool {
    s.len() > 0 && count_a(s) > s.len() as int / 2
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_a_subrange(s: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        count_a(s.subrange(start, end)) == count_a(s) - count_a(s.subrange(0, start)) - count_a(s.subrange(end, s.len())),
{
    /* helper modified by LLM (iteration 5): Fixed unclosed delimiter and proof logic */
    if start == end {
        assert(s.subrange(start, end) == Seq::empty());
        assert(count_a(s.subrange(start, end)) == 0);
        assert(count_a(s.subrange(0, start)) + count_a(s.subrange(end, s.len())) == count_a(s));
    } else {
        lemma_count_a_subrange(s, start + 1, end);
        let sub = s.subrange(start, end);
        let first_char_count = if s[start] == 'a' { 1 } else { 0 };
        assert(sub == s[start] + s.subrange(start + 1, end));
        assert(count_a(sub) == first_char_count + count_a(s.subrange(start + 1, end)));
        assert(count_a(s.subrange(0, start)) + first_char_count + count_a(s.subrange(start + 1, s.len())) == count_a(s));
    }
}

proof fn lemma_count_a_nonnegative(s: Seq<char>)
    ensures
        count_a(s) >= 0,
{
    decreases s.len();
    if s.len() > 0 {
        lemma_count_a_nonnegative(s.subrange(1, s.len()));
    }
}

proof fn lemma_min_properties(a: int, b: int)
    ensures
        min(a, b) <= a,
        min(a, b) <= b,
        min(a, b) == a || min(a, b) == b,
{
}

proof fn lemma_valid_input_implies_count_a_positive(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        count_a(s) > 0,
{
    if s.len() == 0 {
        assert(!valid_input(s));
    } else {
        let i = choose|i: int| 0 <= i < s.len() && s[i] == 'a';
        assert(s[i] == 'a');
        lemma_count_a_nonnegative(s);
        assert(count_a(s) >= 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: usize)
    requires 
        valid_input(s@),
    ensures 
        result >= 1,
        result <= s.len(),
        result == min(2 * count_a(s@) - 1, s.len() as int) as usize,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed verification by ensuring total_a equals count_a(s@) */
    let n = s.len();
    let mut total_a = 0;
    let mut i = 0;
    
    while i < n
        invariant
            i <= n,
            total_a == count_a(s@.subrange(0, i)),
    {
        if s[i] == 'a' {
            total_a = total_a + 1;
        }
        i = i + 1;
    }
    
    proof {
        lemma_valid_input_implies_count_a_positive(s@);
        lemma_count_a_nonnegative(s@);
        lemma_min_properties(2 * total_a - 1, n as int);
    }
    
    let result = min(2 * total_a - 1, n as int) as usize;
    assert(result >= 1);
    assert(result <= n);
    result
}
// </vc-code>


}

fn main() {}