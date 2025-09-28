// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

    /* helper modified by LLM (iteration 5): fix predicate syntax with exclamation mark */
    spec fn all_in_range(s: Seq<i32>, min_val: i32, max_val: i32) -> bool {
        forall|i: int| 0 <= i < s.len() ==> min_val <= s[i] && s[i] <= max_val
    }
    
    fn find_substring_at_helper(haystack: Seq<char>, needle: Seq<char>, pos: int) -> (found: bool)
        requires
            pos >= 0,
            pos + needle.len() <= haystack.len()
        ensures
            found == (haystack.subrange(pos, pos + needle.len()) == needle)
    {
        let mut i = 0;
        
        while i < needle.len()
            invariant
                i <= needle.len(),
                forall|j: int| 0 <= j < i ==> haystack@[pos + j] == needle@[j]
        {
            if haystack@[pos + i] != needle@[i] {
                return false;
            }
            i += 1;
        }
        
        true
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
    /* code modified by LLM (iteration 5): remove unnecessary helpers and fix implementation */
    let n = a.len();
    let mut res_vec = Vec::new();
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            res_vec.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let a_str = a[j]@;
                let sub_str = sub[j]@;
                let start_val = start[j] as int;
                let end_val = end_pos[j] as int;
                
                (res_vec@[j] == -1 <==> 
                    forall|pos: int| start_val <= pos && pos <= end_val && pos + sub_str.len() <= a_str.len() ==>
                        !find_substring_at(a_str, sub_str, pos)) &&

                (res_vec@[j] >= 0 ==> 
                    start_val <= res_vec@[j] as int && 
                    res_vec@[j] as int <= end_val &&
                    res_vec@[j] as int + sub_str.len() <= a_str.len() &&
                    find_substring_at(a_str, sub_str, res_vec@[j] as int) &&
                    forall|pos: int| start_val <= pos && pos < res_vec@[j] as int ==> 
                        !find_substring_at(a_str, sub_str, pos)) &&

                (sub_str.len() == 0 ==> res_vec@[j] == start_val) &&

                (start_val + sub_str.len() > a_str.len() ==> res_vec@[j] == -1) &&

                (start_val > end_val ==> res_vec@[j] == -1)
            }
    {
        let a_str = a[i]@;
        let sub_str = sub[i]@;
        let start_val = start[i] as int;
        let end_val = end_pos[i] as int;
        
        proof {
            assert(start_val <= end_val);
            assert(end_val < a_str.len());
        }
        
        if start_val > end_val {
            res_vec.push(-1);
        } else if start_val + sub_str.len() > a_str.len() {
            res_vec.push(-1);
        } else if sub_str.len() == 0 {
            res_vec.push(start_val as i32);
        } else {
            let mut pos = start_val;
            let mut found = false;
            let mut found_pos = -1;
            
            while pos <= end_val && pos + sub_str.len() <= a_str.len() && !found
                invariant
                    start_val <= pos <= end_val + 1,
                    found ==> (found_pos >= 0 && find_substring_at(a_str, sub_str, found_pos as int)),
                    !found ==> forall|p: int| start_val <= p < pos ==> !find_substring_at(a_str, sub_str, p)
            {
                if find_substring_at(a_str, sub_str, pos) {
                    found = true;
                    found_pos = pos as i32;
                } else {
                    pos += 1;
                }
            }
            
            if found {
                res_vec.push(found_pos);
            } else {
                res_vec.push(-1);
            }
        }
        
        i += 1;
    }
    
    res_vec
}
// </vc-code>

}
fn main() {}