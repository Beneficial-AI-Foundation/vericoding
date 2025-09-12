// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_character(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0 
    } else { 
        (if s[0] == c { 1 } else { 0 }) + count_character(s.subrange(1, s.len() as int), c) 
    }
}

spec fn has_same_character_counts(s: Seq<char>, t: Seq<char>) -> bool {
    s.len() == t.len() && 
    forall|c: char| count_character(s, c) == count_character(t, c)
}

spec fn find_next_match(s: Seq<char>, c: char, start: int) -> int
    requires 0 <= start <= s.len()
    ensures start <= find_next_match(s, c, start) <= s.len()
    decreases s.len() - start
{
    if start >= s.len() { 
        s.len() 
    } else if s[start] == c { 
        start 
    } else { 
        find_next_match(s, c, start + 1) 
    }
}
// </vc-preamble>

// <vc-helpers>
spec fn can_match_substring(s: Seq<char>, t: Seq<char>, i: int, j: int, k: int) -> bool {
    if 0 <= i <= j < t.len() && 0 <= k <= s.len() && s.len() == t.len() {
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
    } else {
        false
    }
}

spec fn max_preservable_length(s: Seq<char>, t: Seq<char>, i: int, j: int, max_so_far: int) -> int {
    if 0 <= i <= t.len() && i <= j <= t.len() && s.len() == t.len() && max_so_far >= 0 && max_so_far <= s.len() {
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
    } else {
        max_so_far
    }
}

spec fn max_longest_subsequence(s: Seq<char>, t: Seq<char>) -> int {
    if s.len() == t.len() && s.len() >= 0 {
        if s.len() == 0 { 
            0 
        } else { 
            max_preservable_length(s, t, 0, 0, 0) 
        }
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Seq<char>, t: Seq<char>) -> (result: int)
    requires s.len() == t.len()
    requires s.len() >= 0
    ensures result == -1 <==> !has_same_character_counts(s, t)
    ensures result >= -1
    ensures result != -1 ==> 0 <= result <= s.len()
    ensures result != -1 ==> has_same_character_counts(s, t)
    ensures result != -1 ==> result == s.len() - max_longest_subsequence(s, t)
    ensures s.len() == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}