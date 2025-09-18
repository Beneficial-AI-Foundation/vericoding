// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added exec helper to compare character slices */
exec fn compare_slices(haystack: &Vec<char>, start: usize, needle: &Vec<char>) -> bool {
    if start + needle.len() > haystack.len() {
        false
    } else {
        let mut i = 0;
        while i < needle.len() 
            invariant i <= needle.len()
            invariant forall|j: int| 0 <= j < i ==> start + j < haystack.len() && haystack@[start + j] == needle@[j]
        {
            if haystack[start + i] != needle[i] {
                return false;
            }
            i += 1;
        }
        true
    }
}
// </vc-helpers>

// <vc-spec>
spec fn find_substring_at(haystack: Seq<char>, needle: Seq<char>, pos: int) -> bool {
    pos >= 0 && pos + needle.len() <= haystack.len() &&
    haystack.subrange(pos, pos + needle.len()) == needle
}

fn find(a: Vec<String>, sub: Vec<String>, start: Vec<i32>, end_pos: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == sub.len() && 
        sub.len() == start.len() && 
        start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            0 <= start[i] && 
            start[i] <= end_pos[i] && 
            end_pos[i] < a[i]@.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {

            (result[i] == -1 <==> 
                forall|pos: int| start[i] <= pos && pos <= end_pos[i] && pos + sub[i]@.len() <= a[i]@.len() ==>
                    !find_substring_at(a[i]@, sub[i]@, pos)) &&

            (result[i] >= 0 ==> 
                start[i] <= result[i] && 
                result[i] <= end_pos[i] &&
                result[i] + sub[i]@.len() <= a[i]@.len() &&
                find_substring_at(a[i]@, sub[i]@, result[i] as int) &&
                forall|pos: int| start[i] <= pos && pos < result[i] ==> 
                    !find_substring_at(a[i]@, sub[i]@, pos)) &&

            (sub[i]@.len() == 0 ==> result[i] == start[i]) &&

            (start[i] + sub[i]@.len() > a[i]@.len() ==> result[i] == -1) &&

            (start[i] > end_pos[i] ==> result[i] == -1)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): replaced slicing with helper function to avoid compilation error */
{
    let mut result = Vec::new();
    for i in 0..a.len() {
        let haystack = a[i].as_str().to_string();
        let needle = sub[i].as_str().to_string();
        let start_idx = start[i] as usize;
        let end_idx = end_pos[i] as usize;
        
        if needle.len() == 0 {
            result.push(start_idx as i32);
            continue;
        }
        
        if start_idx > end_idx || start_idx + needle.len() > haystack.len() {
            result.push(-1);
            continue;
        }
        
        let haystack_chars: Vec<char> = haystack.chars().collect();
        let needle_chars: Vec<char> = needle.chars().collect();
        
        let mut found = -1;
        for pos in start_idx..end_idx + 1 {
            if compare_slices(&haystack_chars, pos, &needle_chars) {
                found = pos as i32;
                break;
            }
        }
        result.push(found);
    }
    result
}
// </vc-code>

}
fn main() {}