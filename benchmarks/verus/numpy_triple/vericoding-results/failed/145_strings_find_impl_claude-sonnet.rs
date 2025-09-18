// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type annotations and sequence indexing */
spec fn chars_match_at(haystack: Seq<char>, needle: Seq<char>, pos: int) -> bool {
    pos >= 0 && pos + needle.len() <= haystack.len() &&
    forall|j: int| 0 <= j < needle.len() ==> haystack[pos + j] == needle[j]
}

proof fn substring_match_equiv(haystack: Seq<char>, needle: Seq<char>, pos: int)
    ensures chars_match_at(haystack, needle, pos) <==> find_substring_at(haystack, needle, pos)
{
    if pos >= 0 && pos + needle.len() <= haystack.len() {
        assert(haystack.subrange(pos, pos + needle.len()) == needle <==> 
               forall|j: int| 0 <= j < needle.len() ==> haystack[pos + j] == needle[j]);
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
{
    /* code modified by LLM (iteration 5): fixed type casting and indexing issues */
    let mut result: Vec<i32> = Vec::new();
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> {
                (result[k] == -1 <==> 
                    forall|pos: int| start[k] <= pos && pos <= end_pos[k] && pos + sub[k]@.len() <= a[k]@.len() ==>
                        !find_substring_at(a[k]@, sub[k]@, pos)) &&
                (result[k] >= 0 ==> 
                    start[k] <= result[k] && 
                    result[k] <= end_pos[k] &&
                    result[k] + sub[k]@.len() <= a[k]@.len() &&
                    find_substring_at(a[k]@, sub[k]@, result[k] as int) &&
                    forall|pos: int| start[k] <= pos && pos < result[k] ==> 
                        !find_substring_at(a[k]@, sub[k]@, pos)) &&
                (sub[k]@.len() == 0 ==> result[k] == start[k]) &&
                (start[k] + sub[k]@.len() <= a[k]@.len() ==> true) &&
                (start[k] > end_pos[k] ==> result[k] == -1)
            }
    {
        if sub[i]@.len() == 0 {
            result.push(start[i]);
        } else {
            let sub_len = sub[i].len() as i32;
            let a_len = a[i].len() as i32;
            
            if start[i] > end_pos[i] || start[i] + sub_len > a_len {
                result.push(-1);
            } else {
                let mut found = -1;
                let mut pos = start[i];
                
                while pos <= end_pos[i] && pos + sub_len <= a_len
                    invariant
                        start[i] as int <= pos as int <= end_pos[i] as int + 1,
                        found == -1,
                        forall|p: int| start[i] as int <= p < pos as int ==> !find_substring_at(a[i] as int @, sub[i] as int @, p)
                {
                    let mut matches = true;
                    let mut j = 0;
                    
                    while j < sub[i].len()
                        invariant
                            0 <= j <= sub[i] as int .len(),
                            matches <==> forall|k: int| 0 <= k < j as int ==> a[i] as int @[pos as int + k] == sub[i] as int @[k],
                            pos + sub_len <= a_len
                    {
                        proof {
                            let pos_int = pos as int;
                            let j_int = j as int;
                            assert(a[i] as int @[pos_int + j_int] != sub[i] as int @[j_int] ==> !matches);
                        }
                        if a[i]@.index(pos as int + j as int) != sub[i]@.index(j as int) {
                            matches = false;
                            break;
                        }
                        j += 1;
                    }
                    
                    if matches {
                        proof {
                            substring_match_equiv(a[i] as int @, sub[i] as int @, pos as int);
                        }
                        found = pos;
                        break;
                    }
                    
                    pos += 1;
                }
                
                result.push(found);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}