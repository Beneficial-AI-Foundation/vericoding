// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add decreases clause to find_next_distinct function */
fn find_next_distinct(s: &[i32], start: usize, value: i32) -> (end: usize)
    requires
        0 <= start <= s.len(),
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
    ensures
        start <= end <= s.len(),
        forall|i: int| start <= i < end ==> s[i] == value,
        end == s.len() || s@[end as int] != value,
    decreases (s.len() - start as int),
{
    let mut end = start;
    while end < s.len()
        decreases s.len() - end as int,
        && s[end] == value
    {
        end += 1;
    }
    end
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() <= 100_000,
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): add decreases clause to main loop */
{
    let mut i: usize = 0;
    let mut expected = 0_i32;
    
    while i < s.len()
        decreases (s.len() - i as int) * 2 + (1000000i32 - expected as int),
        && s[i] == expected
    {
        i = find_next_distinct(s, i, expected);
        expected += 1;
    }
    
    expected
}
// </vc-code>

}
fn main() {}