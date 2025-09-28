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
/* helper modified by LLM (iteration 4): connect occurrences with count properties */
proof fn occurrence_implies_count_ge_one(chars: Seq<char>, idx: int, c: char)
    requires 0 <= idx < chars.len() && chars[idx] == c
    ensures count_char(chars, c) >= 1
    decreases chars.len()
{
    if chars.len() == 0 {
        // impossible due to requires
    } else if idx == 0 {
        assert(chars[0] == c);
        assert(count_char(chars, c) >= 1);
    } else {
        let rest = chars.subrange(1, chars.len() as int);
        occurrence_implies_count_ge_one(rest, idx - 1, c);
        if chars[0] == c {
            assert(count_char(chars, c) >= 1);
        } else {
            // when chars[0] != c, count_char(chars, c) equals count_char(rest, c)
            assert(count_char(chars, c) >= 1);
        }
    }
}

proof fn second_occurrence_implies_count(chars: Seq<char>, i: int, j: int, c: char)
    requires 0 <= i < j < chars.len() && chars[i] == c && chars[j] == c
    ensures count_char(chars, c) >= 2
    decreases chars.len()
{
    if chars.len() == 0 {
        // impossible due to requires
    } else if i == 0 {
        let rest = chars.subrange(1, chars.len() as int);
        // there is an occurrence in rest at j-1
        occurrence_implies_count_ge_one(rest, j - 1, c);
        // chars[0] == c and rest contains at least one c, so total >= 2
        assert(count_char(chars, c) >= 2);
    } else {
        let rest = chars.subrange(1, chars.len() as int);
        second_occurrence_implies_count(rest, i - 1, j - 1, c);
        // result for rest lifts to original sequence
        assert(count_char(chars, c) >= 2);
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
    /* code modified by LLM (iteration 4): iterate and track seen prefix; fixed triggers and invariants */
    let n: usize = s.len();
    let mut idx: usize = 0usize;
    let mut seen: Vec<char> = Vec::new();

    while idx < n
        invariant
            idx <= n,
            has_no_duplicates_up_to(s@, idx as int),
            seen.len() == idx,
            forall|t: int| 0 <= t < idx as int ==> (seen@)[t] == (s@)[t],
        decreases n - idx
    {
        let ch: char = s[idx];

        let mut found: bool = false;
        let mut found_idx: usize = 0usize;
        let mut k: usize = 0usize;
        while k < seen.len()
            invariant
                k <= seen.len(),
                forall|t: int| 0 <= t < k as int ==> (seen@)[t] != ch,
            decreases seen.len() - k
        {
            if seen[k] == ch {
                found = true;
                found_idx = k;
                break;
            }
            k += 1;
        }

        if found {
            proof {
                let chars = s@;
                let fi: int = found_idx as int;
                let cur: int = idx as int;
                assert((seen@)[fi] == (s@)[fi]);
                assert((s@)[cur] == ch);
                assert((seen@)[fi] == ch);
                assert(chars[fi] == ch);
                assert(chars[cur] == ch);
                assert(0 <= fi && fi < cur && cur < chars.len());
                assert(exists|i: int, j: int| 0 <= i < j < chars.len() && chars[i] == ch && chars[j] == ch);
                second_occurrence_implies_count(chars, fi, cur, ch);
                assert(has_no_duplicates_up_to(chars, cur));
            }
            return Some(ch);
        } else {
            seen.push(ch);
            idx += 1;
        }
    }

    proof {
        assert(has_no_duplicates(s@));
    }
    None
}

// </vc-code>

}
fn main() {}