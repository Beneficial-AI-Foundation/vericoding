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
/* helper modified by LLM (iteration 4): Fixed character counting logic and subsequence computation */
proof fn lemma_empty_same_counts()
    ensures
        forall|s: Seq<char>, t: Seq<char>| s.len() == 0 && t.len() == 0 ==> has_same_character_counts(s, t)
{
    assert forall|s: Seq<char>, t: Seq<char>| s.len() == 0 && t.len() == 0 implies #[trigger] has_same_character_counts(s, t) by {
        assert forall|c: char| count_character(s, c) == count_character(t, c) by {
            assert(count_character(s, c) == 0);
            assert(count_character(t, c) == 0);
        }
    }
}

proof fn lemma_count_character_take(s: Seq<char>, c: char, i: int, j: int)
    requires
        0 <= i <= j <= s.len()
    ensures
        count_character(s.take(j), c) == count_character(s.take(i), c) + count_character(s.skip(i).take(j - i), c)
    decreases j - i
{
    if i == j {
        assert(s.skip(i).take(j - i) =~= Seq::<char>::empty());
    } else if i < j {
        lemma_count_character_take(s, c, i + 1, j);
    }
}

fn check_same_counts(s: &Vec<char>, t: &Vec<char>) -> (result: bool)
    requires
        s.len() == t.len()
    ensures
        result == has_same_character_counts(s@, t@)
{
    if s.len() == 0 {
        proof {
            lemma_empty_same_counts();
        }
        return true;
    }
    
    let mut counts_s: Vec<u32> = Vec::new();
    let mut counts_t: Vec<u32> = Vec::new();
    let mut chars: Vec<char> = Vec::new();
    
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            s.len() == t.len(),
            chars.len() == counts_s.len(),
            counts_s.len() == counts_t.len(),
            forall|j: int| 0 <= j < chars.len() ==> counts_s@[j] >= 0,
            forall|j: int| 0 <= j < chars.len() ==> counts_t@[j] >= 0,
        decreases s.len() - i
    {
        let c = s[i];
        let mut found = false;
        let mut idx: usize = 0;
        
        let mut j: usize = 0;
        while j < chars.len()
            invariant
                j <= chars.len(),
                chars.len() == counts_s.len(),
                counts_s.len() == counts_t.len(),
            decreases chars.len() - j
        {
            if chars[j] == c {
                found = true;
                idx = j;
                break;
            }
            j = j + 1;
        }
        
        if found {
            if counts_s[idx] < u32::MAX {
                counts_s[idx] = counts_s[idx] + 1;
            }
        } else {
            chars.push(c);
            counts_s.push(1);
            counts_t.push(0);
        }
        
        i = i + 1;
    }
    
    i = 0;
    while i < t.len()
        invariant
            i <= t.len(),
            s.len() == t.len(),
            chars.len() == counts_s.len(),
            counts_s.len() == counts_t.len(),
        decreases t.len() - i
    {
        let c = t[i];
        let mut found = false;
        let mut idx: usize = 0;
        
        let mut j: usize = 0;
        while j < chars.len()
            invariant
                j <= chars.len(),
                chars.len() == counts_s.len(),
                counts_s.len() == counts_t.len(),
            decreases chars.len() - j
        {
            if chars[j] == c {
                found = true;
                idx = j;
                break;
            }
            j = j + 1;
        }
        
        if found {
            if counts_t[idx] < u32::MAX {
                counts_t[idx] = counts_t[idx] + 1;
            }
        } else {
            return false;
        }
        
        i = i + 1;
    }
    
    let mut k: usize = 0;
    while k < chars.len()
        invariant
            k <= chars.len(),
            chars.len() == counts_s.len(),
            counts_s.len() == counts_t.len(),
        decreases chars.len() - k
    {
        if counts_s[k] != counts_t[k] {
            return false;
        }
        k = k + 1;
    }
    
    true
}

fn compute_max_subsequence_length(s: &Vec<char>, t: &Vec<char>) -> (result: usize)
    requires
        s.len() == t.len(),
        has_same_character_counts(s@, t@)
    ensures
        result as int == max_longest_subsequence(s@, t@),
        result <= s.len()
{
    let n = s.len();
    if n == 0 {
        return 0;
    }
    
    let mut max_len: usize = 0;
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            max_len <= n,
        decreases n - i
    {
        let mut j: usize = i;
        while j < n
            invariant
                i <= j,
                j <= n,
                max_len <= n,
            decreases n - j
        {
            let mut can_match = true;
            let mut used: Vec<bool> = Vec::new();
            let mut k: usize = 0;
            while k < n
                invariant
                    k <= n,
                    used.len() == k,
                decreases n - k
            {
                used.push(false);
                k = k + 1;
            }
            
            let mut ti: usize = i;
            while ti <= j
                invariant
                    i <= ti,
                    ti <= j + 1,
                    used.len() == n,
                decreases j - ti + 1
            {
                if ti > j {
                    break;
                }
                let mut found = false;
                let mut si: usize = 0;
                while si < n
                    invariant
                        si <= n,
                        used.len() == n,
                        ti <= j,
                        ti < n,
                    decreases n - si
                {
                    if !used[si] && s[si] == t[ti] {
                        used[si] = true;
                        found = true;
                        break;
                    }
                    si = si + 1;
                }
                if !found {
                    can_match = false;
                    break;
                }
                ti = ti + 1;
            }
            
            if can_match {
                let current_len = j - i + 1;
                if current_len > max_len {
                    max_len = current_len;
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    max_len
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
    /* code modified by LLM (iteration 4): Improved result calculation with proper bounds checking */
    if s.len() == 0 {
        proof {
            lemma_empty_same_counts();
            assert(max_longest_subsequence(s@, t@) == 0);
        }
        return 0;
    }
    
    if !check_same_counts(&s, &t) {
        return -1;
    }
    
    let max_subseq_len = compute_max_subsequence_length(&s, &t);
    
    proof {
        assert(has_same_character_counts(s@, t@));
        assert(max_subseq_len as int == max_longest_subsequence(s@, t@));
        assert(max_subseq_len <= s.len());
    }
    
    let diff = s.len() - max_subseq_len;
    proof {
        assert(0 <= diff <= s.len());
        assert(diff == s.len() - max_subseq_len);
        assert(diff as int == s.len() as int - max_longest_subsequence(s@, t@));
    }
    
    if s.len() <= i32::MAX as usize {
        let result = diff as i32;
        proof {
            assert(result >= 0);
            assert(result <= s.len() as i32);
            assert(result == s.len() as i32 - max_longest_subsequence(s@, t@) as i32);
        }
        return result;
    }
    
    0
}
// </vc-code>


}

fn main() {}