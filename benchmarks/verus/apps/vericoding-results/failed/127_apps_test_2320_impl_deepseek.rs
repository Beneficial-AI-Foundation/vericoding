// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_character(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0 as int
    } else {
        (if s[0] == c { 1 as int } else { 0 as int }) + count_character(s.skip(1), c)
    }
}

spec fn has_same_character_counts(s: Seq<char>, t: Seq<char>) -> bool {
    s.len() == t.len() && 
    (forall|c: char| count_character(s, c) == count_character(t, c))
}

spec fn find_next_match(s: Seq<char>, c: char, start: int) -> int
    decreases s.len() - start
{
    if start >= s.len() {
        s.len() as int
    } else if s[start] == c {
        start
    } else {
        find_next_match(s, c, start + 1)
    }
}

spec fn can_match_substring(s: Seq<char>, t: Seq<char>, i: int, j: int, k: int) -> bool
    decreases j - i + 1, s.len() - k
{
    if i > j {
        true
    } else if k >= s.len() {
        false
    } else {
        let next_k = find_next_match(s, t[j], k);
        if next_k >= s.len() {
            false
        } else if i == j {
            true
        } else {
            can_match_substring(s, t, i, j-1, next_k+1)
        }
    }
}

spec fn max_preservable_length(s: Seq<char>, t: Seq<char>, i: int, j: int, max_so_far: int) -> int
    decreases t.len() - i, t.len() - j
{
    if i >= t.len() {
        max_so_far
    } else if j >= t.len() {
        max_preservable_length(s, t, i+1, i+1, max_so_far)
    } else {
        let current_len = j - i + 1;
        let can_match = can_match_substring(s, t, i, j, 0);
        let new_max = if can_match && current_len > max_so_far { current_len } else { max_so_far };
        max_preservable_length(s, t, i, j+1, new_max)
    }
}

spec fn max_longest_subsequence(s: Seq<char>, t: Seq<char>) -> int
{
    if s.len() == 0 {
        0 as int
    } else {
        max_preservable_length(s, t, 0, 0, 0)
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_count_character_nonnegative(s: Seq<char>, c: char)
    ensures
        count_character(s, c) >= 0,
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_character_nonnegative(s.skip(1), c);
    }
}

proof fn lemma_count_character_skip_cons(s: Seq<char>, c: char)
    ensures
        count_character(s, c) == (if s.len() > 0 { if s[0] == c { 1 as int } else { 0 as int } } else { 0 as int }) + count_character(s.skip(1), c),
    decreases s.len()
{
}

proof fn lemma_find_next_match_bounds(s: Seq<char>, c: char, start: int)
    requires
        0 <= start <= s.len(),
    ensures
        start <= find_next_match(s, c, start) <= s.len(),
    decreases s.len() - start
{
    if start < s.len() {
        lemma_find_next_match_bounds(s, c, start + 1);
    }
}

proof fn lemma_can_match_substring_properties(s: Seq<char>, t: Seq<char>, i: int, j: int, k: int)
    requires
        0 <= i <= j < t.len(),
        0 <= k <= s.len(),
    ensures
        if can_match_substring(s, t, i, j, k) {
            exists|l: int| k <= l < s.len() && s[l] == t[j] && (i == j || can_match_substring(s, t, i, j-1, l+1))
        } else {
            true
        },
    decreases j - i + 1, s.len() - k
{
    if i <= j && k < s.len() {
        lemma_find_next_match_bounds(s, t[j], k);
        let next_k = find_next_match(s, t[j], k);
        if next_k < s.len() && i < j {
            lemma_can_match_substring_properties(s, t, i, j-1, next_k+1);
        }
    }
}

proof fn lemma_max_preservable_length_nonnegative(s: Seq<char>, t: Seq<char>, i: int, j: int, max_so_far: int)
    requires
        0 <= i <= t.len(),
        0 <= j <= t.len(),
        max_so_far >= 0,
    ensures
        max_preservable_length(s, t, i, j, max_so_far) >= 0,
    decreases t.len() - i, t.len() - j
{
    if i < t.len() && j < t.len() {
        lemma_max_preservable_length_nonnegative(s, t, i, j+1, max_so_far);
    }
    if i < t.len() && j >= t.len() {
        lemma_max_preservable_length_nonnegative(s, t, i+1, i+1, max_so_far);
    }
}

proof fn lemma_max_preservable_length_upper_bound(s: Seq<char>, t: Seq<char>, i: int, j: int, max_so_far: int)
    requires
        0 <= i <= t.len(),
        0 <= j <= t.len(),
        0 <= max_so_far <= t.len(),
    ensures
        max_preservable_length(s, t, i, j, max_so_far) <= t.len(),
    decreases t.len() - i, t.len() - j
{
    if i < t.len() && j < t.len() {
        lemma_max_preservable_length_upper_bound(s, t, i, j+1, max_so_far);
    }
    if i < t.len() && j >= t.len() {
        lemma_max_preservable_length_upper_bound(s, t, i+1, i+1, max_so_far);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, t: Vec<char>) -> (result: i32)
    requires 
        s.len() == t.len(),
        s.len() >= 0,
    ensures 
        result == -1 <==> !has_same_character_counts(s@, t@),
        result >= -1,
        result != -1 ==> 0 <= result <= s.len() as i32,
        result != -1 ==> has_same_character_counts(s@, t@),
        result != -1 ==> result == s.len() as i32 - max_longest_subsequence(s@, t@) as i32,
        s.len() == 0 ==> result == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed type conversion and function call issues */
    if s.len() == 0 {
        return 0;
    }
    
    if !has_same_character_counts(s@, t@) {
        return -1;
    }
    
    let mut max_len = 0;
    let mut i = 0;
    let t_len = t.len() as int;
    let s_len = s.len() as int;
    let t_seq = t@;
    let s_seq = s@;
    
    while i < t_len
        invariant
            0 <= i <= t_len,
            0 <= max_len <= s_len,
    {
        let mut j = i;
        while j < t_len
            invariant
                i <= j <= t_len,
                max_len >= 0,
        {
            let current_len = (j - i + 1);
            if can_match_substring(s_seq, t_seq, i, j, 0) && current_len > max_len {
                max_len = current_len;
            }
            j += 1;
        }
        i += 1;
    }
    
    let result = (s_len - max_len) as i32;
    result
}
// </vc-code>


}

fn main() {}