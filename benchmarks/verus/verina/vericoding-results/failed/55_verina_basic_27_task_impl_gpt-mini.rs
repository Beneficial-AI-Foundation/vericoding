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
/* helper modified by LLM (iteration 5): find previous index of same char before idx */
fn find_prev_index(s: &Vec<char>, idx: int) -> Option<int>
    requires
        0 <= idx < s@.len(),
    ensures
        match result {
            Some(k) => 0 <= k < idx && s@[k] == s@[idx],
            None => forall|k: int| 0 <= k < idx ==> s@[k] != s@[idx],
        },
{
    let mut k: int = 0;
    while k < idx
        invariant
            0 <= k && k <= idx,
            forall|t: int| 0 <= t < k ==> s@[t] != s@[idx],
        decreases idx - k
    {
        if s[k as usize] == s[idx as usize] {
            return Some(k);
        }
        k = k + 1;
    }
    None
}

/* helper modified by LLM (iteration 5): monotonicity of count_char for suffixes */
fn count_char_suffix_leq(chars: Seq<char>, k: int, c: char)
    requires
        0 <= k <= chars.len(),
    ensures
        count_char(chars, c) >= count_char(chars.subrange(k, chars.len()), c),
    decreases
        k
{
    if k == 0 {
        // trivial: suffix is whole sequence, count >= itself
    } else {
        // k > 0
        let rest = chars.subrange(1, chars.len());
        count_char_suffix_leq(rest, k - 1, c);
        // chars.len() >= 1 here
        if chars[0] == c {
            // count_char(chars, c) == 1 + count_char(rest, c)
            assert(count_char(chars, c) == 1 + count_char(rest, c));
            // by induction on rest: count_char(rest, c) >= count_char(rest.subrange(k-1, rest.len()))
            assert(count_char(rest, c) >= count_char(rest.subrange(k - 1, rest.len())));
            // rest.subrange(k-1, rest.len()) == chars.subrange(k, chars.len())
            assert(rest.subrange(k - 1, rest.len()) == chars.subrange(k, chars.len()));
            assert(count_char(chars, c) >= 1 + count_char(rest.subrange(k - 1, rest.len())));
            assert(count_char(chars, c) >= count_char(chars.subrange(k, chars.len())));
        } else {
            // count_char(chars, c) == count_char(rest, c)
            assert(count_char(chars, c) == count_char(rest, c));
            assert(count_char(rest, c) >= count_char(rest.subrange(k - 1, rest.len())));
            assert(rest.subrange(k - 1, rest.len()) == chars.subrange(k, chars.len()));
            assert(count_char(chars, c) >= count_char(chars.subrange(k, chars.len())));
        }
    }
}

/* helper modified by LLM (iteration 5): nonempty suffix contains at least one occurrence if the first element equals c */
fn count_char_suffix_ge1(chars: Seq<char>, k: int, c: char)
    requires
        0 <= k < chars.len(),
        chars[k] == c,
    ensures
        count_char(chars.subrange(k, chars.len()), c) >= 1,
{
    let suffix = chars.subrange(k, chars.len());
    // suffix.len() > 0 and suffix[0] == c
    let rest = suffix.subrange(1, suffix.len());
    assert(suffix[0] == c);
    assert(count_char(suffix, c) == 1 + count_char(rest, c));
    assert(count_char(suffix, c) >= 1);
}

/* helper modified by LLM (iteration 5): show count_char >= 2 given two distinct indices with same char */
fn count_char_at_least_two(chars: Seq<char>, i: int, j: int, c: char)
    requires
        0 <= i < j < chars.len(),
        chars[i] == c,
        chars[j] == c,
    ensures
        count_char(chars, c) >= 2,
{
    // Relate whole sequence to suffix at i
    count_char_suffix_leq(chars, i, c);
    // suffix at i has first element == c
    let suffix_i = chars.subrange(i, chars.len());
    let suffix_i_rest = suffix_i.subrange(1, suffix_i.len());
    assert(suffix_i[0] == c);
    // count_char(suffix_i, c) == 1 + count_char(suffix_i_rest, c)
    assert(count_char(suffix_i, c) == 1 + count_char(suffix_i_rest, c));
    // Show suffix_i_rest contains at least the occurrence at original j
    // index in suffix_i_rest corresponding to j is j - (i + 1)
    let k_in_rest: int = j - (i + 1);
    // 0 <= k_in_rest < suffix_i_rest.len()
    assert(0 <= k_in_rest && k_in_rest < suffix_i_rest.len());
    // apply monotonicity on suffix_i_rest to compare with chars.subrange(j, len)
    count_char_suffix_leq(suffix_i_rest, k_in_rest, c);
    // and show the final suffix at j has at least one occurrence
    count_char_suffix_ge1(chars, j, c);
    // Chain inequalities:
    // count_char(chars, c) >= count_char(suffix_i, c) == 1 + count_char(suffix_i_rest, c) >= 1 + count_char(chars.subrange(j, chars.len()), c) >= 1 + 1
    assert(count_char(suffix_i_rest, c) >= count_char(chars.subrange(j, chars.len()), c));
    assert(count_char(suffix_i, c) >= 1 + count_char(chars.subrange(j, chars.len()), c));
    // count_char(chars, c) >= count_char(suffix_i, c)
    assert(count_char(chars, c) >= count_char(suffix_i, c));
    // and count_char(chars.subrange(j,len), c) >= 1 by previous helper
    assert(count_char(chars.subrange(j, chars.len()), c) >= 1);
    assert(count_char(chars, c) >= 1 + 1);
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
/* code modified by LLM (iteration 5): scan for first repeated char and prove properties */
{
    let n = s@.len();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            has_no_duplicates_up_to(s@, i),
        decreases n - i
    {
        if let Some(k) = find_prev_index(s, i) {
            proof {
                let chars = s@;
                let c = chars[i];
                assert(0 <= k && k < i && i < chars.len());
                assert(chars[k] == c);
                // prove there are at least two occurrences
                count_char_at_least_two(chars, k, i, c);
                // show existence of two indices
                assert(exists|u: int, v: int| 0 <= u < v < chars.len() && chars[u] == c && chars[v] == c);
                // has_no_duplicates_up_to up to second index (i) holds from loop invariant
                assert(has_no_duplicates_up_to(chars, i));
            }
            return Some(s[i as usize]);
        }
        i = i + 1;
    }
    proof {
        let chars = s@;
        assert(has_no_duplicates(chars));
    }
    None
}

// </vc-code>

}
fn main() {}