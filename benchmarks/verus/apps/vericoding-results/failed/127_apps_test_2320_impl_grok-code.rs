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
/* helper modified by LLM (iteration 4): replaced .contains() with manual loop to avoid unsupported method */
fn find_next_match_exec(s: &Vec<char>, c: char, start: usize) -> usize {
    let mut i = start;
    while i < s.len() {
        if s[i] == c {
            return i;
        }
        i += 1;
    }
    return s.len();
}

fn can_match_substring_exec(s: &Vec<char>, t: &Vec<char>, i: usize, j: usize, k: usize) -> bool
    decreases j - i + 1, s.len() - k
{
    if i > j {
        true
    } else if k >= s.len() {
        false
    } else {
        let next_k = find_next_match_exec(s, t[j], k);
        if next_k >= s.len() {
            false
        } else if i == j {
            true
        } else {
            can_match_substring_exec(s, t, i, j-1, next_k+1)
        }
    }
}

fn max_preservable_length_exec(s: &Vec<char>, t: &Vec<char>, i: usize, j: usize, max_so_far: usize) -> usize
    decreases t.len() - i, t.len() - j
{
    if i >= t.len() {
        max_so_far
    } else if j >= t.len() {
        max_preservable_length_exec(s, t, i+1, i+1, max_so_far)
    } else {
        let current_len = j - i + 1;
        let can_match = can_match_substring_exec(s, t, i, j, 0);
        let new_max = if can_match && current_len > max_so_far {
            current_len
        } else {
            max_so_far
        };
        max_preservable_length_exec(s, t, i, j+1, new_max)
    }
}

fn max_longest_subsequence_exec(s: &Vec<char>, t: &Vec<char>) -> usize {
    if s.len() == 0 {
        0
    } else {
        max_preservable_length_exec(s, t, 0, 0, 0)
    }
}

/* helper modified by LLM (iteration 5): fixed ref patterns in loops by omitting ref in pattern */
fn has_same_character_counts_exec(s: Vec<char>, t: Vec<char>) -> bool {
    if s.len() != t.len() {
        return false;
    }
    let mut chars: Vec<char> = Vec::new();
    for i in 0..s.len() {
        let c = s[i];
        let mut found = false;
        for ch in &chars {
            if *ch == c {
                found = true;
                break;
            }
        }
        if !found {
            chars.push(c);
        }
    }
    for i in 0..t.len() {
        let c = t[i];
        let mut found = false;
        for ch in &chars {
            if *ch == c {
                found = true;
                break;
            }
        }
        if !found {
            chars.push(c);
        }
    }
    for i in 0..chars.len() {
        let c = chars[i];
        let mut count_s = 0;
        let mut count_t = 0;
        for j in 0..s.len() {
            if s[j] == c {
                count_s += 1;
            }
            if t[j] == c {
                count_t += 1;
            }
        }
        if count_s != count_t {
            return false;
        }
    }
    true
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
/* code modified by LLM (iteration 4): implemented main logic to check character counts and compute result */
{
    let has_same = has_same_character_counts_exec(s.clone(), t.clone());
    if !has_same {
        -1
    } else {
        let len = max_longest_subsequence_exec(&s, &t);
        (s.len() as i32) - (len as i32)
    }
}
// </vc-code>


}

fn main() {}