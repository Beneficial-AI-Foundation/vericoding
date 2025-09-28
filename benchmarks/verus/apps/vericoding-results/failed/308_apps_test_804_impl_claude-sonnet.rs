// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>, k: int) -> bool {
    1 <= k <= 26 && 1 <= s.len() <= 1000 && 
    forall|i: int| 0 <= i < s.len() ==> 'a' <= #[trigger] s[i] <= 'z'
}

spec fn unique_chars(s: Seq<char>) -> Set<char> {
    s.to_set()
}

spec fn min_changes(s: Seq<char>, k: int) -> int {
    let unique = unique_chars(s);
    if k <= unique.len() { 0 } else { k - unique.len() }
}

spec fn is_impossible(s: Seq<char>, k: int) -> bool {
    s.len() < k
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added stronger invariants and proof structure */
fn char_to_usize(c: char) -> (result: usize)
    requires 'a' <= c <= 'z'
    ensures result < 26
{
    (c as u8 - 97u8) as usize
}

fn count_unique_chars(s: &Vec<char>) -> (result: usize)
    requires forall|i: int| 0 <= i < s@.len() ==> 'a' <= #[trigger] s@[i] <= 'z'
    ensures result == unique_chars(s@).len()
{
    let mut seen = [false; 26];
    let mut count = 0usize;
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            forall|j: int| 0 <= j < s@.len() ==> 'a' <= #[trigger] s@[j] <= 'z',
            count <= 26,
            count as int == s@.subrange(0, i as int).to_set().len(),
        decreases s.len() - i
    {
        let c = s[i];
        let idx = char_to_usize(c);
        if !seen[idx] {
            seen[idx] = true;
            count += 1;
        }
        i += 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
        assert(count as int == s@.to_set().len());
    }
    
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8) -> (result: String)
    requires valid_input(s@, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): ensured proper type conversion and bounds */
    let k_usize = k as usize;
    let s_len = s.len();
    
    if s_len < k_usize {
        return "-1".to_string();
    }
    
    let unique_count = count_unique_chars(&s);
    
    if k_usize <= unique_count {
        return "0".to_string();
    }
    
    let changes_needed = k_usize - unique_count;
    changes_needed.to_string()
}
// </vc-code>


}

fn main() {}