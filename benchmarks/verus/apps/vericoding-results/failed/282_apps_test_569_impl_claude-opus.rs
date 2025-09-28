// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 1
}

spec fn count_distinct_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: i32)
    requires 
        valid_input(n as int, s@)
    ensures 
        n > 26 ==> result == -1,
        n <= 26 ==> result >= 0 && result < n as i32,
        n <= 26 ==> result == s@.len() as i32 - count_distinct_chars(s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clauses to both while loops */
    if n > 26 {
        return -1;
    }
    
    let mut seen: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < 26
        invariant
            seen.len() == i,
            forall |j: int| 0 <= j < i ==> seen@[j] == false,
        decreases 26 - i
    {
        seen.push(false);
        i = i + 1;
    }
    
    let mut distinct_count: usize = 0;
    let mut j: usize = 0;
    
    while j < n
        invariant
            j <= n,
            seen.len() == 26,
            distinct_count <= j,
            distinct_count <= 26,
            forall |k: int| 0 <= k < j ==> s@[k] >= 'a' && s@[k] <= 'z',
        decreases n - j
    {
        let c = s[j];
        assert(c >= 'a' && c <= 'z');
        let idx = (c as u8 - 'a' as u8) as usize;
        
        if !seen[idx] {
            seen.set(idx, true);
            distinct_count = distinct_count + 1;
        }
        j = j + 1;
    }
    
    (n as i32 - distinct_count as i32)
}
// </vc-code>


}

fn main() {}