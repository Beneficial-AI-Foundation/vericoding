// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type conversions in exec code */
spec fn matches_at_position(haystack: Seq<char>, needle: Seq<char>, pos: int) -> bool {
    haystack.subrange(pos, pos + needle.len()) == needle
}

fn find_substring_in_range(haystack: &Vec<char>, needle: &Vec<char>, start: i32, end_pos: i32) -> (result: i32)
    requires
        0 <= start <= end_pos,
        end_pos < haystack.len(),
    ensures
        result == -1 || (start <= result <= end_pos && result + needle.len() <= haystack.len()),
        result >= 0 ==> find_substring_at(haystack@, needle@, result as int),
        result >= 0 ==> forall|pos: int| start <= pos < result ==> !find_substring_at(haystack@, needle@, pos),
        result == -1 ==> forall|pos: int| start <= pos && pos <= end_pos && pos + needle.len() <= haystack.len() ==> !find_substring_at(haystack@, needle@, pos),
        needle.len() == 0 ==> result == start,
        start as int + needle.len() > haystack.len() ==> result == -1,
{
    if needle.len() == 0 {
        return start;
    }
    
    if start as usize + needle.len() > haystack.len() {
        return -1;
    }
    
    let mut pos = start;
    
    while pos <= end_pos && (pos as usize + needle.len()) <= haystack.len()
        invariant
            start <= pos <= end_pos + 1,
            pos <= haystack.len(),
            forall|j: int| start <= j < pos ==> !find_substring_at(haystack@, needle@, j),
    {
        let mut matches = true;
        let mut i: usize = 0;
        
        while i < needle.len()
            invariant
                0 <= i <= needle.len(),
                matches <==> forall|j: int| 0 <= j < i ==> haystack@[pos + j] == needle@[j],
        {
            if haystack[pos as usize + i] != needle[i] {
                matches = false;
                break;
            }
            i = i + 1;
        }
        
        if matches {
            proof {
                assert(haystack@.subrange(pos as int, pos + needle.len()) == needle@);
            }
            return pos;
        }
        
        pos = pos + 1;
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
/* code modified by LLM (iteration 5): fixed type mismatches with proper casts and indexing */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (result[j] == -1 <==> 
                    forall|pos: int| start[j] <= pos && pos <= end_pos[j] && pos + sub[j]@.len() <= a[j]@.len() ==>
                        !find_substring_at(a[j]@, sub[j]@, pos)) &&
                (result[j] >= 0 ==> 
                    start[j] <= result[j] && 
                    result[j] <= end_pos[j] &&
                    result[j] + sub[j]@.len() <= a[j]@.len() &&
                    find_substring_at(a[j]@, sub[j]@, result[j] as int) &&
                    forall|pos: int| start[j] <= pos && pos < result[j] ==> 
                        !find_substring_at(a[j]@, sub[j]@, pos)) &&
                (sub[j]@.len() == 0 ==> result[j] == start[j]) &&
                (start[j] + sub[j]@.len() > a[j]@.len() ==> result[j] == -1) &&
                (start[j] > end_pos[j] ==> result[j] == -1)
            },
    {
        if start[i] > end_pos[i] {
            result.push(-1);
        } else {
            let mut haystack_vec: Vec<char> = Vec::new();
            let mut j: usize = 0;
            while j < a[i]@.len() as usize
                invariant
                    0 <= j <= a[i]@.len(),
                    haystack_vec.len() == j as nat,
                    forall|k: int| 0 <= k < j as int ==> haystack_vec@[k] == a[i]@[k],
            {
                haystack_vec.push(a[i]@[j as int]);
                j = j + 1;
            }
            
            let mut needle_vec: Vec<char> = Vec::new();
            let mut j: usize = 0;
            while j < sub[i]@.len() as usize
                invariant
                    0 <= j <= sub[i]@.len(),
                    needle_vec.len() == j as nat,
                    forall|k: int| 0 <= k < j as int ==> needle_vec@[k] == sub[i]@[k],
            {
                needle_vec.push(sub[i]@[j as int]);
                j = j + 1;
            }
            
            let found = find_substring_in_range(&haystack_vec, &needle_vec, start[i], end_pos[i]);
            result.push(found);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}