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
fn count_chars_vec(v: &Vec<char>, c: char) -> (count: usize)
    ensures count == count_character(v@, c)
{
    let mut count = 0;
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            count == count_character(v@.take(i as int), c),
    {
        if v[i] == c {
            count += 1;
        }
        i += 1;
    }
    count
}

fn same_char_counts(s: &Vec<char>, t: &Vec<char>) -> (result: bool)
    requires s.len() == t.len()
    ensures result == has_same_character_counts(s@, t@)
{
    if s.len() == 0 {
        return true;
    }
    
    let mut chars_seen: Vec<char> = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            forall|j: int| 0 <= j < chars_seen.len() ==> 
                count_character(s@, chars_seen@[j]) == count_character(t@, chars_seen@[j]),
    {
        let c = s[i];
        let mut found = false;
        let mut j = 0;
        
        while j < chars_seen.len()
            invariant
                j <= chars_seen.len(),
                found == exists|k: int| 0 <= k < j && chars_seen@[k] == c,
        {
            if chars_seen[j] == c {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            let s_count = count_chars_vec(s, c);
            let t_count = count_chars_vec(t, c);
            if s_count != t_count {
                return false;
            }
            chars_seen.push(c);
        }
        i += 1;
    }
    
    true
}

fn find_lcs_length(s: &Vec<char>, t: &Vec<char>) -> (result: usize)
    requires s.len() == t.len()
    ensures result <= s.len()
{
    /* helper modified by LLM (iteration 5): use Vec::with_capacity and manual initialization to avoid vec! macro */
    if s.len() == 0 {
        return 0;
    }
    
    let n = s.len();
    let mut dp: Vec<Vec<usize>> = Vec::with_capacity(n + 1);
    
    let mut k = 0;
    while k <= n
        invariant
            k <= n + 1,
            dp.len() == k,
    {
        let mut row: Vec<usize> = Vec::with_capacity(n + 1);
        let mut l = 0;
        while l <= n
            invariant
                l <= n + 1,
                row.len() == l,
        {
            row.push(0);
            l += 1;
        }
        dp.push(row);
        k += 1;
    }
    
    let mut i = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            dp.len() == n + 1,
            forall|k: int| 0 <= k < dp.len() ==> dp[k].len() == n + 1,
    {
        let mut j = 1;
        while j <= n
            invariant
                1 <= j <= n + 1,
                i <= n + 1,
                dp.len() == n + 1,
                forall|k: int| 0 <= k < dp.len() ==> dp[k].len() == n + 1,
        {
            let new_val = if s[i-1] == t[j-1] {
                dp[i-1][j-1] + 1
            } else {
                if dp[i-1][j] > dp[i][j-1] { dp[i-1][j] } else { dp[i][j-1] }
            };
            dp[i].set(j, new_val);
            j += 1;
        }
        i += 1;
    }
    
    dp[n][n]
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
    /* code modified by LLM (iteration 5): fixed compilation error */
    if s.len() == 0 {
        return 0;
    }
    
    if !same_char_counts(&s, &t) {
        return -1;
    }
    
    let lcs_len = find_lcs_length(&s, &t);
    (s.len() - lcs_len) as i32
}
// </vc-code>


}

fn main() {}