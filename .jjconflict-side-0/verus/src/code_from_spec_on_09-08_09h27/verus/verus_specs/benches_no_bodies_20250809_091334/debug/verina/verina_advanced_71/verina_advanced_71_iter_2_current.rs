use vstd::prelude::*;

verus! {

// Helper function to count ones in a sequence
spec fn count_ones(s: Seq<char>) -> nat 
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        (if s[0] == '1' { 1nat } else { 0nat }) + count_ones(s.subrange(1, s.len() as int))
    }
}

// Precondition: string contains only '0' and '1'
spec fn shortest_beautiful_substring_precond(s: Seq<char>, k: nat) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

// Generate all substrings
spec fn all_substrings(s: Seq<char>) -> Set<Seq<char>> {
    Set::new(|sub: Seq<char>| {
        exists|i: int, j: int| {
            &&& 0 <= i <= j <= s.len()
            &&& sub == s.subrange(i, j)
        }
    })
}

// Check if a substring is beautiful (has exactly k ones)
spec fn is_beautiful(sub: Seq<char>, k: nat) -> bool {
    count_ones(sub) == k
}

// Executive function - basic implementation without full verification
fn shortest_beautiful_substring(s: Vec<char>, k: u32) -> (result: Vec<char>)
    requires 
        shortest_beautiful_substring_precond(s@, k as nat),
{
    let mut shortest: Vec<char> = Vec::new();
    let mut min_len: usize = usize::MAX;
    
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for outer loop */
    while i < s.len()
        invariant i <= s.len()
        decreases s.len() - i
    {
        let mut ones_count = 0;
        let mut j = i;
        
        /* code modified by LLM (iteration 1): added decreases clause for inner loop */
        while j < s.len()
            invariant 
                i <= j <= s.len(),
                ones_count <= k,
            decreases s.len() - j
        {
            if s[j] == '1' {
                ones_count += 1;
            }
            
            if ones_count == k {
                let current_len = j - i + 1;
                if current_len < min_len {
                    min_len = current_len;
                    shortest = Vec::new();
                    let mut idx = i;
                    /* code modified by LLM (iteration 1): added decreases clause for copy loop */
                    while idx <= j
                        invariant 
                            i <= idx <= j + 1,
                            j < s.len(),
                        decreases j + 1 - idx
                    {
                        shortest.push(s[idx]);
                        idx += 1;
                    }
                }
                break;
            }
            j += 1;
        }
        i += 1;
    }
    
    shortest
}

} // verus!

fn main() {}