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
    /* code modified by LLM (iteration 5): Removed explicit triggers to let Verus infer them automatically */
    let mut ab_found = false;
    let mut ba_found = false;
    let mut ab_index: usize = 0;
    let mut ba_index: usize = 0;
    
    if input.len() < 2 {
        return vec!['N', 'O'];
    }
    
    let mut i: usize = 0;
    while i < input.len() - 1
        invariant
            0 <= i <= input.len(),
            !ab_found ==> forall|j: int| 
                0 <= j && j < i && j + 1 < input@.len() ==> 
                !(input@[j] == 'A' && input@[j + 1] == 'B'),
            ab_found ==> ab_index < input.len() - 1 && 
                input@[ab_index as int] == 'A' && input@[ab_index as int + 1] == 'B',
            ab_found ==> forall|j: int| 
                0 <= j && j < ab_index ==> 
                !(input@[j] == 'A' && input@[j + 1] == 'B'),
        decreases input.len() - i
    {
        if input[i] == 'A' && input[i + 1] == 'B' && !ab_found {
            ab_found = true;
            ab_index = i;
        }
        i = i + 1;
    }
    
    let mut j: usize = 0;
    while j < input.len() - 1
        invariant
            0 <= j <= input.len(),
            !ba_found ==> forall|k: int| 
                0 <= k && k < j && k + 1 < input@.len() ==> 
                !(input@[k] == 'B' && input@[k + 1] == 'A'),
            ba_found ==> ba_index < input.len() - 1 && 
                input@[ba_index as int] == 'B' && input@[ba_index as int + 1] == 'A',
            ba_found ==> forall|k: int| 
                0 <= k && k < ba_index ==> 
                !(input@[k] == 'B' && input@[k + 1] == 'A'),
        decreases input.len() - j
    {
        if input[j] == 'B' && input[j + 1] == 'A' && !ba_found {
            ba_found = true;
            ba_index = j;
        }
        j = j + 1;
    }
    
    if ab_found && ba_found {
        if (ab_index + 2 <= ba_index) || (ba_index + 2 <= ab_index) {
            proof {
                if ab_index + 2 <= ba_index {
                    assert(find_index(input@, seq!['A', 'B']) == ab_index as int);
                    assert(input@.subrange(ab_index as int + 2, input@.len() as int)[ba_index as int - ab_index - 2] == 'B');
                    assert(input@.subrange(ab_index as int + 2, input@.len() as int)[ba_index as int - ab_index - 1] == 'A');
                    assert(count_substring(input@.subrange(ab_index as int + 2, input@.len() as int), seq!['B', 'A']) > 0);
                } else {
                    assert(find_index(input@, seq!['B', 'A']) == ba_index as int);
                    assert(input@.subrange(ba_index as int + 2, input@.len() as int)[ab_index as int - ba_index - 2] == 'A');
                    assert(input@.subrange(ba_index as int + 2, input@.len() as int)[ab_index as int - ba_index - 1] == 'B');
                    assert(count_substring(input@.subrange(ba_index as int + 2, input@.len() as int), seq!['A', 'B']) > 0);
                }
                assert(has_non_overlapping_ab_and_ba(input@));
            }
            vec!['Y', 'E', 'S']
        } else {
            proof {
                assert(!has_non_overlapping_ab_and_ba(input@));
            }
            vec!['N', 'O']
        }
    } else {
        proof {
            if !ab_found {
                assert(find_index(input@, seq!['A', 'B']) == -1);
            }
            if !ba_found {
                assert(find_index(input@, seq!['B', 'A']) == -1);
            }
            assert(!has_non_overlapping_ab_and_ba(input@));
        }
        vec!['N', 'O']
    }
}
// </vc-code>


}

fn main() {}