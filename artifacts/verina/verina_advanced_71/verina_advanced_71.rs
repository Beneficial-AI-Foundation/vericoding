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
    let mut best: Vec<char> = Vec::new();
    let mut found = false;
    
    // Generate all substrings and find the best beautiful one
    let n = s.len();
    let mut i = 0usize;
    
    while i < n
        decreases n - i
    {
        let mut j = i;
        while j < n
            decreases n - j
        {
            let mut substring: Vec<char> = Vec::new();
            let mut k_idx = i;
            while k_idx <= j && k_idx < s.len()
                decreases s.len() - k_idx
            {
                substring.push(s[k_idx]);
                k_idx = k_idx + 1;
            }
            
            // Count ones in the substring
            let mut count = 0u32;
            let mut idx = 0usize;
            while idx < substring.len() && count <= k
                decreases substring.len() - idx
            {
                if substring[idx] == '1' {
                    if count < u32::MAX {
                        count = count + 1;
                    }
                }
                idx = idx + 1;
            }
            
            if count == k {
                if !found {
                    best = substring;
                    found = true;
                } else {
                    // Simple comparison: prefer shorter strings
                    if substring.len() < best.len() {
                        best = substring;
                    }
                }
            }
            
            if j < n - 1 {
                j = j + 1;
            } else {
                break;
            }
        }
        i = i + 1;
    }

    best
}

} // verus!

fn main() {}