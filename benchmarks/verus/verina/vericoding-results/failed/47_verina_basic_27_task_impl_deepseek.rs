// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_char(chars: Seq<char>, c: char) -> nat 
    decreases chars.len()
{
    if chars.len() == 0 {
        0
    } else if chars[0] == c {
        1 + count_char(chars.subrange(1, chars.len() as int), c)
    } else {
        count_char(chars.subrange(1, chars.len() as int), c)
    }
}

spec fn has_no_duplicates_up_to(chars: Seq<char>, end_idx: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < end_idx ==> #[trigger] chars[i] != #[trigger] chars[j]
}

spec fn has_no_duplicates(chars: Seq<char>) -> bool {
    forall|i: int, j: int| 0 <= i < j < chars.len() ==> #[trigger] chars[i] != #[trigger] chars[j]
}

spec fn first_occurrence_index(chars: Seq<char>, c: char) -> int {
    choose|i: int| 0 <= i < chars.len() && chars[i] == c
}

spec fn second_occurrence_exists(chars: Seq<char>, c: char) -> bool {
    exists|i: int, j: int| 0 <= i < j < chars.len() && #[trigger] chars[i] == c && #[trigger] chars[j] == c
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type annotation in lemma_count_char_subrange */
proof fn lemma_count_char_subrange(chars: Seq<char>, c: char, start: int, len: int)
    requires
        0 <= start <= start + len <= chars.len(),
    ensures
        count_char(chars.subrange(start, start + len), c) == count_char(chars, c) - count_char(chars.subrange(0, start), c) - count_char(chars.subrange(start + len, chars.len() as int), c),
    decreases len
{
    if len == 0 {
        assert(chars.subrange(start, start) == Seq::<char>::empty());
        assert(count_char(chars.subrange(start, start), c) == 0);
    } else {
        lemma_count_char_subrange(chars, c, start + 1, len - 1);
    }
}

proof fn lemma_has_no_duplicates_up_to_implies(chars: Seq<char>, end_idx: int)
    requires
        0 <= end_idx <= chars.len(),
        has_no_duplicates_up_to(chars, end_idx),
    ensures
        forall|i: int, j: int| 0 <= i < j < end_idx ==> #[trigger] chars[i] != #[trigger] chars[j],
{
}

proof fn lemma_no_duplicates_up_to_extend(chars: Seq<char>, end_idx: int)
    requires
        0 <= end_idx < chars.len(),
        has_no_duplicates_up_to(chars, end_idx),
        forall|i: int| 0 <= i < end_idx ==> chars[i] != chars[end_idx],
    ensures
        has_no_duplicates_up_to(chars, end_idx + 1),
{
}

/* helper modified by LLM (iteration 5): Add executable helper for character lookup with proper type */
fn char_at_index(s: &Vec<char>, idx: usize) -> (c: char)
    requires idx < s.len(),
    ensures c == s@[idx as int]
{
    s[idx]
}
// </vc-helpers>

// <vc-spec>
fn find_first_repeated_char(s: &Vec<char>) -> (result: Option<char>)
    ensures match result {
        Some(c) => {
            let chars = s@;
            count_char(chars, c) >= 2 &&
            second_occurrence_exists(chars, c) &&
            {
                let first_idx = first_occurrence_index(chars, c);
                let second_idx = choose|j: int| first_idx < j < chars.len() && chars[j] == c;
                has_no_duplicates_up_to(chars, second_idx)
            }
        },
        None => {
            has_no_duplicates(s@)
        }
    }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix loop invariants and ensure proper verification */
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            has_no_duplicates_up_to(s@, i as int),
        decreases s.len() - i
    {
        let c = char_at_index(s, i);
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i,
                forall|k: int| 0 <= k < j as int ==> s@[k] != c,
            decreases i - j
        {
            let prev_char = char_at_index(s, j);
            if prev_char == c {
                return Some(c);
            }
            j = j + 1;
        }
        proof {
            lemma_no_duplicates_up_to_extend(s@, i as int);
        }
        i = i + 1;
    }
    None
}
// </vc-code>

}
fn main() {}