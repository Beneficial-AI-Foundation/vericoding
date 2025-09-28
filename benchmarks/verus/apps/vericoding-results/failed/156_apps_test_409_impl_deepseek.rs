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
proof fn lemma_find_index_subrange(s: Seq<char>, pattern: Seq<char>, i: int)
    requires
        0 <= i <= s.len() - pattern.len(),
        s.subrange(i, i + pattern.len() as int) =~= pattern,
    ensures
        find_index(s, pattern) >= 0,
    decreases s.len() - i
{
    if i == 0 {
        // Base case: pattern found at index 0
    } else {
        lemma_find_index_subrange(s.subrange(1, s.len() as int), pattern, i - 1);
    }
}

proof fn lemma_count_substring_nonzero_implies_exists(s: Seq<char>, pattern: Seq<char>)
    requires
        pattern.len() > 0,
    ensures
        count_substring(s, pattern) > 0 <==> exists|i: int| 0 <= i <= s.len() - pattern.len() && s.subrange(i, i + pattern.len() as int) =~= pattern,
    decreases s.len()
{
    if s.len() < pattern.len() {
        // Base case: empty or too short
    } else {
        if s.subrange(0, pattern.len() as int) =~= pattern {
            // Pattern found at beginning
        } else {
            lemma_count_substring_nonzero_implies_exists(s.subrange(1, s.len() as int), pattern);
        }
    }
}

proof fn lemma_subrange_relation(s: Seq<char>, start1: int, start2: int, len: int)
    requires
        0 <= start1 <= start2 <= s.len(),
        len >= 0,
        start2 + len <= s.len(),
    ensures
        s.subrange(start2, start2 + len).subrange(0, len) =~= s.subrange(start2, start2 + len),
        s.subrange(start1, s.len()).subrange(start2 - start1, start2 - start1 + len) =~= s.subrange(start2, start2 + len),
{
    // Built-in axioms should handle this
}

/* helper modified by LLM (iteration 5): fix ghost function syntax with proper sequence comparison */
proof fn ghost_find_first_occurrence(s: Seq<char>, pattern: Seq<char>) -> int
    ensures
        (result == -1) ==> (forall|i: int| 0 <= i <= s.len() - pattern.len() ==> s.subrange(i, i + pattern.len()) != pattern),
        (result >= 0) ==> (0 <= result <= s.len() - pattern.len() && s.subrange(result, result + pattern.len()) == pattern)
{
    if s.len() < pattern.len() {
        -1
    } else {
        find_index(s, pattern)
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
{
    /* code modified by LLM (iteration 5): use usize iterators and check both patterns with fixed syntax */
    let ab_pattern = vec!['A', 'B'];
    let ba_pattern = vec!['B', 'A'];
    
    let mut ab_indices: Vec<usize> = Vec::new();
    let mut ba_indices: Vec<usize> = Vec::new();
    
    let mut i: usize = 0;
    while i < input.len() - 1
        invariant
            0 <= i <= input@.len(),
    {
        if input[i] == 'A' && input[i + 1] == 'B' {
            ab_indices.push(i);
        }
        if input[i] == 'B' && input[i + 1] == 'A' {
            ba_indices.push(i);
        }
        i += 1;
    }
    
    let mut non_overlapping = false;
    
    if !ab_indices.is_empty() && !ba_indices.is_empty() {
        let mut j: usize = 0;
        while j < ab_indices.len()
            invariant
                0 <= j <= ab_indices@.len(),
        {
            let mut k: usize = 0;
            while k < ba_indices.len()
                invariant
                    0 <= k <= ba_indices@.len(),
            {
                let ab_idx = ab_indices[j];
                let ba_idx = ba_indices[k];
                if ab_idx + 2 <= ba_idx || ba_idx + 2 <= ab_idx {
                    non_overlapping = true;
                }
                k += 1;
            }
            j += 1;
        }
    }
    
    if non_overlapping {
        vec!['Y', 'E', 'S']
    } else {
        vec!['N', 'O']
    }
}
// </vc-code>


}

fn main() {}