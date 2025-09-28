// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_substring(s: Seq<char>, pattern: Seq<char>) -> nat 
    decreases s.len()
{
    if pattern.len() == 0 || s.len() < pattern.len() {
        0
    } else if s.subrange(0, pattern.len() as int) =~= pattern {
        1 + count_substring(s.subrange(1, s.len() as int), pattern)
    } else {
        count_substring(s.subrange(1, s.len() as int), pattern)
    }
}

spec fn find_index(s: Seq<char>, pattern: Seq<char>) -> int 
    decreases s.len()
{
    if pattern.len() == 0 || s.len() < pattern.len() {
        -1
    } else if s.subrange(0, pattern.len() as int) =~= pattern {
        0
    } else {
        let rest = find_index(s.subrange(1, s.len() as int), pattern);
        if rest == -1 { -1 } else { 1 + rest }
    }
}

spec fn has_non_overlapping_ab_and_ba(s: Seq<char>) -> bool {
    let ab_pattern = seq!['A', 'B'];
    let ba_pattern = seq!['B', 'A'];
    let ab_index = find_index(s, ab_pattern);
    let ba_index = find_index(s, ba_pattern);

    (ab_index >= 0 && ba_index >= 0) &&
    (
        (ab_index >= 0 && ab_index + 2 < s.len() && count_substring(s.subrange(ab_index + 2, s.len() as int), ba_pattern) > 0) ||
        (ba_index >= 0 && ba_index + 2 < s.len() && count_substring(s.subrange(ba_index + 2, s.len() as int), ab_pattern) > 0)
    )
}

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed type mismatch in requires and ensures clauses by adding proper type casts to align usize and int types */
exec fn find_index_exec(s: &Vec<char>, pattern: Vec<char>, start: usize) -> (res: Option<usize>)
    requires
        start <= s.len(),
        pattern.len() == 2
    ensures
        if pattern == vec!['A', 'B'] {
            let pat_spec = seq!['A', 'B'];
            res == if find_index(s@.subrange(start as int, s@.len() as int), pat_spec) >= 0 {
                Some(find_index(s@.subrange(start as int, s@.len() as int), pat_spec) as usize)
            } else {
                None
            }
        } else if pattern == vec!['B', 'A'] {
            let pat_spec = seq!['B', 'A'];
            res == if find_index(s@.subrange(start as int, s@.len() as int), pat_spec) >= 0 {
                Some(find_index(s@.subrange(start as int, s@.len() as int), pat_spec) as usize)
            } else {
                None
            }
        } else {
            true
        }
    decreases s.len() - start
{
    if start + pattern.len() > s.len() {
        None
    } else if s[start..start + pattern.len()] == pattern[..] {
        Some(start)
    } else {
        find_index_exec(s, pattern, start + 1)
    }
}

exec fn count_substring_exec(s: &Vec<char>, pattern: Vec<char>, start: usize) -> (count: usize)
    requires
        start <= s.len(),
        pattern.len() == 2,
        find_index_exec(s, pattern.clone(), start).is_none() ==> 
            count_substring(s@.subrange(start as int, s@.len() as int), pattern@) == 0,
        find_index_exec(s, pattern.clone(), start).is_some() ==> {
            let idx = find_index_exec(s, pattern.clone(), start).unwrap();
            ((1 as usize) + count_substring_exec(s, pattern.clone(), idx + 1)) as int == count_substring(s@.subrange(start as int, s@.len() as int), pattern@)
        }
    ensures
        (pattern == vec!['A', 'B'] || pattern == vec!['B', 'A']) ==> 
            (count as int) == count_substring(s@.subrange(start as int, s@.len() as int), pattern@)
    decreases s.len() - start
{
    if start + pattern.len() > s.len() {
        0
    } else if s[start..start + pattern.len()] == pattern[..] {
        1 + count_substring_exec(s, pattern, start + 1)
    } else {
        count_substring_exec(s, pattern, start + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures 
        result@ == seq!['Y', 'E', 'S'] || result@ == seq!['N', 'O'],
        has_non_overlapping_ab_and_ba(input@) <==> result@ == seq!['Y', 'E', 'S']
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Updated proof assertions to properly align types with helper function spec changes */
{
    let ab_pattern = vec!['A', 'B'];
    let ba_pattern = vec!['B', 'A'];
    let ab_index = find_index_exec(&input, ab_pattern.clone(), 0);
    let ba_index = find_index_exec(&input, ba_pattern.clone(), 0);
    proof {
        let ab_ghost = seq!['A', 'B'];
        let ba_ghost = seq!['B', 'A'];
        assert(ab_index.is_some() ==> ab_index.unwrap() as int == find_index(input@, ab_ghost));
        assert(ab_index.is_none() ==> find_index(input@, ab_ghost) == -1);
        assert(ba_index.is_some() ==> ba_index.unwrap() as int == find_index(input@, ba_ghost));
        assert(ba_index.is_none() ==> find_index(input@, ba_ghost) == -1);
    }
    if ab_index.is_some() && ba_index.is_some() {
        let ab_idx = ab_index.unwrap();
        let ba_idx = ba_index.unwrap();
        let has_ba_after_ab = count_substring_exec(&input, ba_pattern.clone(), ab_idx + 2) > 0;
        let has_ab_after_ba = count_substring_exec(&input, ab_pattern.clone(), ba_idx + 2) > 0;
        proof {
            let ab_ghost = seq!['A', 'B'];
            let ba_ghost = seq!['B', 'A'];
            assert(has_ba_after_ab == (count_substring(input@.subrange((ab_idx + 2) as int, input@.len() as int), ba_ghost) > 0));
            assert(has_ab_after_ba == (count_substring(input@.subrange((ba_idx + 2) as int, input@.len() as int), ab_ghost) > 0));
        }
        if has_ba_after_ab || has_ab_after_ba {
            vec!['Y', 'E', 'S']
        } else {
            vec!['N', 'O']
        }
    } else {
        vec!['N', 'O']
    }
}
// </vc-code>


}

fn main() {}