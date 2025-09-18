// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Correct `find_subsequence` loop condition and post-condition, ensure `start_idx` is returned when pattern is empty. */
spec fn find_subsequence(text: Seq<char>, pattern: Seq<char>, start_idx: int, end_idx: int) -> (result: int)
    requires
        0 <= start_idx <= end_idx,
        end_idx <= text.len(),
        pattern.len() > 0
    ensures
        start_idx <= result,
        result <= end_idx,
        (result + pattern.len() as int <= text.len() as int && text.subrange(result as nat, (result + pattern.len() as int) as nat) == pattern)
        || (result == end_idx && (! exists |k: int| (
            start_idx <= k <= end_idx - pattern.len() as int
            && text.subrange(k as nat, (k + pattern.len() as int) as nat) == pattern
        ))),
        (result + pattern.len() as int <= text.len() as int && text.subrange(result as nat, (result + pattern.len() as int) as nat) == pattern) ==> {
            forall|k: int|
                start_idx <= k < result
                && k + pattern.len() as int <= text.len() as int
                ==> text.subrange(k as nat, (k + pattern.len() as int) as nat) != pattern
        }
{
    if pattern.len() == 0 {
        start_idx
    } else {
        let mut i = start_idx;
        while i + pattern.len() as int <= end_idx + 1
            invariant
                start_idx <= i as int,
                i + pattern.len() as int <= end_idx + 1,
                forall|k: int|
                    start_idx <= k < i
                    && k + pattern.len() as int <= text.len() as int
                    ==> text.subrange(k as nat, (k + pattern.len() as int) as nat) != pattern
        {
            if i + pattern.len() as int <= text.len() as int && text.subrange(i as nat, (i + pattern.len() as int) as nat) == pattern {
                return i;
            }
            i = i + 1;
        }
        end_idx
    }
}
// </vc-helpers>

// <vc-spec>
fn index(a: Vec<Seq<char>>, sub: Vec<Seq<char>>, start: Vec<int>, end_pos: Vec<int>) -> (result: Vec<int>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& start[i] >= 0 
            &&& start[i] <= end_pos[i]
            &&& end_pos[i] <= a[i].len() as int
            &&& sub[i].len() > 0
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& result[i] >= 0
            &&& start[i] <= result[i] <= end_pos[i]
            &&& result[i] + sub[i].len() as int <= a[i].len() as int
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by casting `a.len()` to `usize` for `while` loop condition */
{
    let mut results = Vec::new();
    let mut i: int = 0;
    while i < a.len() as int
        invariant
            0 <= i <= a.len() as int,
            results.len() == i as nat,
            forall|j: int| 0 <= j < i ==> {
                let r_j = results[j as usize];
                &&& start[j as usize] <= r_j
                &&& r_j <= end_pos[j as usize]
                &&& r_j + sub[j as usize].len() as int <= a[j as usize].len() as int
                &&& r_j >= 0
            }
    {
        let current_a_seq = a[i as usize];
        let current_sub_seq = sub[i as usize];
        let current_start_int = start[i as usize];
        let current_end_pos_int = end_pos[i as usize];

        let found_index = find_subsequence(current_a_seq, current_sub_seq, current_start_int, current_end_pos_int);

        results.push(found_index);
        i = i + 1;
    }
    results
}
// </vc-code>

}
fn main() {}