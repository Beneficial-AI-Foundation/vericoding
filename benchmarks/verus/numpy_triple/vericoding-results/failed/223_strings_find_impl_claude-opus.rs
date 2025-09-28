// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed string iteration without using collect() */
fn string_to_chars(s: &String) -> (result: Vec<char>)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == s@[i],
{
    let mut chars = Vec::new();
    let mut i: usize = 0;
    
    while i < s@.len()
        invariant
            i <= s@.len(),
            chars@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> chars@[j] == s@[j],
        decreases s@.len() - i,
    {
        chars.push(s@[i as int]);
        i = i + 1;
    }
    
    chars
}

fn find_single(s: &Vec<char>, pattern: &Vec<char>, start_idx: i32, end_idx: i32) -> (result: i32)
    requires
        0 <= start_idx,
        start_idx <= end_idx,
        end_idx < s.len(),
    ensures
        result == -1 <==> forall|pos: int| start_idx as int <= pos && pos <= end_idx as int && pos + pattern.len() <= s.len() ==> !find_substring_at(s@, pattern@, pos),
        result >= 0 ==> start_idx as int <= result as int && result as int <= end_idx as int && result as int + pattern.len() <= s.len() && find_substring_at(s@, pattern@, result as int) && forall|pos: int| start_idx as int <= pos && pos < result as int ==> !find_substring_at(s@, pattern@, pos),
        pattern.len() == 0 ==> result == start_idx,
        start_idx as int + pattern.len() > s.len() ==> result == -1,
        start_idx > end_idx ==> result == -1,
{
    if start_idx > end_idx {
        return -1;
    }
    
    if pattern.len() == 0 {
        return start_idx;
    }
    
    if start_idx as usize + pattern.len() > s.len() {
        return -1;
    }
    
    let mut i: i32 = start_idx;
    
    while i <= end_idx && (i as usize) + pattern.len() <= s.len()
        invariant
            start_idx <= i,
            i <= end_idx + 1,
            forall|pos: int| start_idx as int <= pos && pos < i as int && pos + pattern.len() <= s.len() ==> !find_substring_at(s@, pattern@, pos),
        decreases end_idx as int - i as int + 1,
    {
        let mut matches = true;
        let mut j: usize = 0;
        
        while j < pattern.len()
            invariant
                j <= pattern.len(),
                matches <==> forall|k: int| 0 <= k && k < j as int ==> s@[i as int + k] == pattern@[k],
            decreases pattern.len() - j,
        {
            if s[i as usize + j] != pattern[j] {
                matches = false;
                break;
            }
            j = j + 1;
        }
        
        if matches {
            assert(s@.subrange(i as int, i as int + pattern.len() as int) == pattern@);
            return i;
        }
        
        i = i + 1;
    }
    
    -1
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
                forall|pos: int| start[i] as int <= pos && pos <= end_pos[i] as int && pos + sub[i]@.len() <= a[i]@.len() ==>
                    !find_substring_at(a[i]@, sub[i]@, pos)) &&

            (result[i] >= 0 ==> 
                start[i] as int <= result[i] as int && 
                result[i] as int <= end_pos[i] as int &&
                result[i] as int + sub[i]@.len() <= a[i]@.len() &&
                find_substring_at(a[i]@, sub[i]@, result[i] as int) &&
                forall|pos: int| start[i] as int <= pos && pos < result[i] as int ==> 
                    !find_substring_at(a[i]@, sub[i]@, pos)) &&

            (sub[i]@.len() == 0 ==> result[i] == start[i]) &&

            (start[i] as int + sub[i]@.len() > a[i]@.len() ==> result[i] == -1) &&

            (start[i] > end_pos[i] ==> result[i] == -1)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed in main code */
    let mut result: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            a.len() == sub.len(),
            sub.len() == start.len(),
            start.len() == end_pos.len(),
            forall|i: int| 0 <= i < a.len() ==> 0 <= start[i] && start[i] <= end_pos[i] && end_pos[i] < a[i]@.len(),
            forall|i: int| 0 <= i < idx as int ==> {
                (result[i] == -1 <==> forall|pos: int| start[i] as int <= pos && pos <= end_pos[i] as int && pos + sub[i]@.len() <= a[i]@.len() ==> !find_substring_at(a[i]@, sub[i]@, pos)) &&
                (result[i] >= 0 ==> start[i] as int <= result[i] as int && result[i] as int <= end_pos[i] as int && result[i] as int + sub[i]@.len() <= a[i]@.len() && find_substring_at(a[i]@, sub[i]@, result[i] as int) && forall|pos: int| start[i] as int <= pos && pos < result[i] as int ==> !find_substring_at(a[i]@, sub[i]@, pos)) &&
                (sub[i]@.len() == 0 ==> result[i] == start[i]) &&
                (start[i] as int + sub[i]@.len() > a[i]@.len() ==> result[i] == -1) &&
                (start[i] > end_pos[i] ==> result[i] == -1)
            },
        decreases a.len() - idx,
    {
        let a_chars = string_to_chars(&a[idx]);
        let sub_chars = string_to_chars(&sub[idx]);
        let pos = find_single(&a_chars, &sub_chars, start[idx], end_pos[idx]);
        result.push(pos);
        idx = idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}