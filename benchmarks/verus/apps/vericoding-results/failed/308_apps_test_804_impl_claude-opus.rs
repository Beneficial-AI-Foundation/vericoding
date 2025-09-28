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

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>, k: i8) -> (result: String)
    requires valid_input(s@, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat type usage - convert to usize for executable code */
    let n = s.len();
    
    if n < k as usize {
        return "impossible".to_string();
    }
    
    let mut unique_set: Set<char> = Set::empty();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            unique_set == s@.subrange(0, i as int).to_set(),
            forall|j: int| 0 <= j < i ==> unique_set.contains(s@[j]),
        decreases n - i
    {
        unique_set = unique_set.insert(s[i]);
        i = i + 1;
    }
    
    let unique_count_nat = unique_set.len();
    
    if k as usize <= unique_count_nat as usize {
        return "0".to_string();
    } else {
        let changes = (k as usize) - (unique_count_nat as usize);
        return changes.to_string();
    }
}
// </vc-code>


}

fn main() {}