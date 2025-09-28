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
/* helper modified by LLM (iteration 5): bound on max_preservable_length result */
proof fn max_preservable_length_tbound(s: Seq<char>, t: Seq<char>, i: int, j: int, max_so_far: int)
    requires
        0 <= i,
        i <= t.len(),
        0 <= j,
        j <= t.len(),
        0 <= max_so_far,
        max_so_far <= t.len(),
    ensures
        max_preservable_length(s, t, i, j, max_so_far) <= t.len(),
    decreases
        t.len() - i,
        t.len() - j
{
    proof {
        if i >= t.len() {
            // result is max_so_far which is <= t.len()
        } else if j >= t.len() {
            max_preservable_length_tbound(s, t, i+1, i+1, max_so_far);
        } else {
            max_preservable_length_tbound(s, t, i, j+1, max_so_far);
        }
    }
}

/* helper modified by LLM (iteration 5): bounds for max_longest_subsequence */
proof fn max_longest_subsequence_bounds(s: Seq<char>, t: Seq<char>)
    requires
        s.len() == t.len(),
    ensures
        0 <= max_longest_subsequence(s, t) && max_longest_subsequence(s, t) <= s.len(),
    decreases
        s.len()
{
    proof {
        if s.len() == 0 {
            // definition returns 0
        } else {
            max_preservable_length_tbound(s, t, 0, 0, 0);
        }
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
/* code modified by LLM (iteration 5): compute max preservable length at runtime and return difference */
{
    if s.len() == 0 {
        0
    } else if !has_same_character_counts(s@, t@) {
        -1
    } else {
        let n = s.len();
        let m = t.len();
        let mut best: usize = 0;

        let mut i: usize = 0;
        while i < m
            invariant
                0 <= i,
                i <= m,
                best <= m,
            decreases
                m - i
        {
            let mut j: usize = i;
            while j < m
                invariant
                    i <= j,
                    j <= m,
                    best <= m,
                decreases
                    m - j
            {
                // check whether t[i..=j] is a subsequence of s
                let mut k: usize = 0;
                let mut idx: usize = i;
                let mut ok: bool = true;
                while idx < j + 1
                    invariant
                        i <= idx,
                        idx <= j + 1,
                        k <= n + 1,
                    decreases
                        (j + 1) - idx
                {
                    let target = t[idx];
                    let mut found: bool = false;
                    while k < n
                        invariant
                            k <= n,
                        decreases
                            n - k
                    {
                        if s[k] == target {
                            found = true;
                            k += 1;
                            break;
                        } else {
                            k += 1;
                        }
                    }
                    if !found {
                        ok = false;
                        break;
                    }
                    idx += 1;
                }

                if ok {
                    let len = j - i + 1;
                    if len > best {
                        best = len;
                    }
                }

                j += 1;
            }

            i += 1;
        }

        let res = (n as i32) - (best as i32);
        res
    }
}

// </vc-code>


}

fn main() {}