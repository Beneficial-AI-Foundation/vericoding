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
proof fn exists_one_implies_count_ge_one(chars: Seq<char>, c: char, k: int) requires 0 <= k < chars.len() && chars[k] == c ensures count_char(chars, c) >= 1 decreases chars.len() {
    if chars.len() == 0 {
    } else {
        if k == 0 {
            let tail = chars.subrange(1, chars.len() as int);
            assert(count_char(chars, c) == 1 + count_char(tail, c));
        } else {
            let tail = chars.subrange(1, chars.len() as int);
            exists_one_implies_count_ge_one(tail, c, k - 1);
            if chars[0] == c {
                assert(count_char(chars, c) == 1 + count_char(tail, c));
            } else {
                assert(count_char(chars, c) == count_char(tail, c));
            }
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
proof fn exists_two_implies_count_ge_two(chars: Seq<char>, c: char, i: int, j: int) requires 0 <= i < j < chars.len() && chars[i] == c && chars[j] == c ensures count_char(chars, c) >= 2 decreases chars.len() {
    if chars.len() == 0 {
    } else {
        if i == 0 {
            let tail = chars.subrange(1, chars.len() as int);
            // j > 0 so j-1 valid in tail
            exists_one_implies_count_ge_one(tail, c, j - 1);
            assert(count_char(chars, c) == 1 + count_char(tail, c));
            assert(count_char(chars, c) >= 2);
        } else {
            let tail = chars.subrange(1, chars.len() as int);
            exists_two_implies_count_ge_two(tail, c, i - 1, j - 1);
            if chars[0] == c {
                assert(count_char(chars, c) == 1 + count_char(tail, c));
            } else {
                assert(count_char(chars, c) == count_char(tail, c));
            }
        }
    }
}
// </vc-code>

}
fn main() {}