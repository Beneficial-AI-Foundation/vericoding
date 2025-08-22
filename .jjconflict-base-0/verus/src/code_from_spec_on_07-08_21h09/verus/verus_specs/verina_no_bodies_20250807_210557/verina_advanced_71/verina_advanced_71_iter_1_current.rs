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

// Helper function to count ones in a Vec
fn count_ones_vec(v: &Vec<char>) -> (result: u32)
    ensures result == count_ones(v@)
{
    let mut count = 0;
    let mut i = 0;
    
    while i < v.len()
        invariant 
            0 <= i <= v.len(),
            count == count_ones(v@.subrange(0, i as int))
    {
        if v[i] == '1' {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

// Helper function to compare vectors lexicographically
fn is_lexicographically_smaller(a: &Vec<char>, b: &Vec<char>) -> (result: bool)
{
    let mut i = 0;
    while i < a.len() && i < b.len()
        invariant 0 <= i <= a.len() && i <= b.len()
    {
        if a[i] < b[i] {
            return true;
        } else if a[i] > b[i] {
            return false;
        }
        i = i + 1;
    }
    a.len() < b.len()
}

// Executive function - basic implementation without full verification
fn shortest_beautiful_substring(s: Vec<char>, k: u32) -> (result: Vec<char>)
    requires 
        shortest_beautiful_substring_precond(s@, k as nat),
{
    if k == 0 {
        return Vec::new();
    }
    
    let mut best_result: Vec<char> = Vec::new();
    let mut found = false;
    
    // Try all possible substrings
    let mut start = 0;
    while start < s.len()
        invariant 0 <= start <= s.len()
    {
        let mut end = start;
        while end < s.len()
            invariant start <= end <= s.len()
        {
            // Extract substring from start to end+1
            let mut substring = Vec::new();
            let mut i = start;
            while i <= end
                invariant start <= i <= end + 1 <= s.len()
            {
                substring.push(s[i]);
                i = i + 1;
            }
            
            // Check if this substring has exactly k ones
            let ones_count = count_ones_vec(&substring);
            if ones_count == k {
                if !found || substring.len() < best_result.len() || 
                   (substring.len() == best_result.len() && is_lexicographically_smaller(&substring, &best_result)) {
                    best_result = substring;
                    found = true;
                }
            }
            
            end = end + 1;
        }
        start = start + 1;
    }
    
    best_result
}

} // verus!

fn main() {}