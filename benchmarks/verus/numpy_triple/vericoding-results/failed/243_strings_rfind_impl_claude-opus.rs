// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn string_starts_with(s: Seq<char>, prefix: Seq<char>, start_pos: int) -> bool {
    start_pos >= 0 && start_pos + prefix.len() <= s.len() &&
    forall|i: int| 0 <= i < prefix.len() ==> s[start_pos + i] == prefix[i]
}

fn rfind(a: Vec<String>, sub: Vec<String>, start: Vec<i32>, end_pos: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < start.len() ==> 0 <= start[i] && start[i] <= end_pos[i],
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> (
            /* Basic range constraint: result is -1 or within string bounds */
            (result[i] == -1 || (0 <= result[i] && result[i] < a[i]@.len())) &&
            /* If result is -1, no occurrence of substring within the specified range */
            (result[i] == -1 ==> 
                forall|j: int| start[i] <= j && j + sub[i]@.len() <= end_pos[i] + 1 && 
                               j + sub[i]@.len() <= a[i]@.len() ==> 
                    !string_starts_with(a[i]@, sub[i]@, j)) &&
            /* If result is non-negative, it's the rightmost valid occurrence */
            (result[i] >= 0 ==> 
                /* The result is within the search range */
                start[i] <= result[i] && 
                result[i] + sub[i]@.len() <= end_pos[i] + 1 &&
                /* The substring matches at this position */
                string_starts_with(a[i]@, sub[i]@, result[i] as int) &&
                /* This is the rightmost occurrence within the range */
                (forall|j: int| result[i] < j && j + sub[i]@.len() <= end_pos[i] + 1 && 
                                start[i] <= j && j + sub[i]@.len() <= a[i]@.len() ==> 
                    !string_starts_with(a[i]@, sub[i]@, j)))
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed int type usage in executable code */
    let mut result = Vec::<i32>::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
            forall|k: int| 0 <= k < start.len() ==> 0 <= start[k] && start[k] <= end_pos[k],
            forall|k: int| 0 <= k < i ==> (
                (result[k] == -1 || (0 <= result[k] && result[k] < a[k]@.len())) &&
                (result[k] == -1 ==> 
                    forall|j: int| start[k] <= j && j + sub[k]@.len() <= end_pos[k] + 1 && 
                                   j + sub[k]@.len() <= a[k]@.len() ==> 
                        !string_starts_with(a[k]@, sub[k]@, j)) &&
                (result[k] >= 0 ==> 
                    start[k] <= result[k] && 
                    result[k] + sub[k]@.len() <= end_pos[k] + 1 &&
                    string_starts_with(a[k]@, sub[k]@, result[k] as int) &&
                    (forall|j: int| result[k] < j && j + sub[k]@.len() <= end_pos[k] + 1 && 
                                    start[k] <= j && j + sub[k]@.len() <= a[k]@.len() ==> 
                        !string_starts_with(a[k]@, sub[k]@, j)))
            ),
    {
        let s = &a[i];
        let pattern = &sub[i];
        let start_pos = start[i];
        let end = end_pos[i];
        
        let mut found_pos: i32 = -1;
        
        if pattern.unicode_len() == 0 {
            if start_pos <= end && start_pos <= s.unicode_len() as i32 {
                found_pos = start_pos;
            }
        } else if pattern.unicode_len() <= s.unicode_len() && start_pos <= end {
            let mut j = start_pos;
            let max_start = if (end + 1 - pattern.unicode_len() as i32) < (s.unicode_len() as i32 - pattern.unicode_len() as i32) {
                end + 1 - pattern.unicode_len() as i32
            } else {
                s.unicode_len() as i32 - pattern.unicode_len() as i32
            };
            
            while j <= max_start
                invariant
                    start_pos <= j <= max_start + 1,
                    max_start == if (end + 1 - pattern.unicode_len() as i32) < (s.unicode_len() as i32 - pattern.unicode_len() as i32) {
                        end + 1 - pattern.unicode_len() as i32
                    } else {
                        s.unicode_len() as i32 - pattern.unicode_len() as i32
                    },
                    pattern.unicode_len() > 0,
                    pattern.unicode_len() <= s.unicode_len(),
                    found_pos == -1 || (start_pos <= found_pos && found_pos <= max_start && string_starts_with(s@, pattern@, found_pos as int)),
                    forall|k: int| found_pos < k && k < j && k + pattern@.len() <= end + 1 && k + pattern@.len() <= s@.len() ==> !string_starts_with(s@, pattern@, k),
            {
                let mut matches = true;
                let mut k: usize = 0;
                
                while k < pattern.unicode_len()
                    invariant
                        0 <= k <= pattern.unicode_len(),
                        j >= 0 && j + pattern.unicode_len() as i32 <= s.unicode_len() as i32,
                        matches == (forall|m: int| 0 <= m < k ==> s@[(j as int) + m] == pattern@[m]),
                {
                    let s_idx = (j as usize) + k;
                    if s_idx >= s.unicode_len() || s.unicode_get(s_idx) != pattern.unicode_get(k) {
                        matches = false;
                        break;
                    }
                    k = k + 1;
                }
                
                if matches {
                    found_pos = j;
                }
                j = j + 1;
            }
        }
        
        result.push(found_pos);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}