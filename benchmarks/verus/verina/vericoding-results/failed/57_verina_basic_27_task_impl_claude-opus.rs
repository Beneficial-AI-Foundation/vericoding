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
proof fn lemma_count_char_at_least_two(chars: Seq<char>, c: char, i: int, j: int)
    requires
        0 <= i < j < chars.len(),
        chars[i] == c,
        chars[j] == c,
    ensures
        count_char(chars, c) >= 2,
    decreases chars.len()
{
    if i == 0 {
        assert(chars[0] == c);
        let rest = chars.subrange(1, chars.len() as int);
        assert(rest[j - 1] == c);
        lemma_count_char_positive(rest, c, j - 1);
    } else {
        let rest = chars.subrange(1, chars.len() as int);
        lemma_count_char_at_least_two(rest, c, i - 1, j - 1);
    }
}

proof fn lemma_count_char_positive(chars: Seq<char>, c: char, idx: int)
    requires
        0 <= idx < chars.len(),
        chars[idx] == c,
    ensures
        count_char(chars, c) >= 1,
    decreases chars.len()
{
    if idx == 0 {
        assert(chars[0] == c);
    } else {
        let rest = chars.subrange(1, chars.len() as int);
        lemma_count_char_positive(rest, c, idx - 1);
    }
}

/* helper modified by LLM (iteration 5): Added lemma for count_char in subrange */
proof fn lemma_count_char_subrange_one(chars: Seq<char>, idx: int)
    requires
        0 <= idx < chars.len(),
        forall|i: int, j: int| 0 <= i < j < idx ==> chars[i] != chars[j],
        forall|i: int| 0 <= i < idx ==> chars[i] != chars[idx],
    ensures
        count_char(chars.subrange(0, idx + 1), chars[idx]) == 1,
    decreases idx + 1
{
    if idx == 0 {
        assert(chars.subrange(0, 1).len() == 1);
        assert(chars.subrange(0, 1)[0] == chars[0]);
    } else {
        let sub = chars.subrange(0, idx + 1);
        assert(sub[idx] == chars[idx]);
        assert forall|i: int| 0 <= i < idx implies sub[i] != chars[idx] by {
            assert(sub[i] == chars[i]);
        }
    }
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
    /* code modified by LLM (iteration 5): Fixed loop invariants and assertions */
    let mut seen = Vec::<char>::new();
    let mut idx = 0;
    
    while idx < s.len()
        invariant
            0 <= idx <= s.len(),
            seen@.len() == idx,
            forall|k: int| 0 <= k < idx ==> seen@[k] == s@[k],
            has_no_duplicates(seen@),
            forall|i: int, j: int| 0 <= i < j < idx ==> s@[i] != s@[j],
        decreases s.len() - idx
    {
        let c = s[idx];
        let mut found = false;
        let mut j = 0;
        
        while j < seen.len()
            invariant
                0 <= j <= seen.len(),
                seen@.len() == idx,
                idx < s.len(),
                c == s@[idx as int],
                forall|k: int| 0 <= k < idx ==> seen@[k] == s@[k],
                found ==> exists|k: int| 0 <= k < j && seen@[k] == c,
                !found ==> forall|k: int| 0 <= k < j ==> seen@[k] != c,
            decreases seen.len() - j
        {
            if seen[j] == c {
                found = true;
                proof {
                    assert(j < idx);
                    assert(seen@[j as int] == s@[j as int]);
                    assert(s@[j as int] == c);
                    assert(s@[idx as int] == c);
                    lemma_count_char_at_least_two(s@, c, j as int, idx as int);
                    assert(second_occurrence_exists(s@, c));
                    assert(has_no_duplicates_up_to(s@, idx as int));
                }
                return Some(c);
            }
            j = j + 1;
        }
        
        proof {
            assert(forall|k: int| 0 <= k < idx ==> seen@[k] != c);
            assert(forall|k: int| 0 <= k < idx ==> s@[k] != c);
            lemma_count_char_subrange_one(s@, idx as int);
        }
        
        seen.push(c);
        idx = idx + 1;
    }
    
    proof {
        assert(has_no_duplicates(s@));
    }
    None
}
// </vc-code>

}
fn main() {}