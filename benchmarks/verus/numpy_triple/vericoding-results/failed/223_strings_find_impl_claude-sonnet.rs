// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn substring_matches(haystack: Seq<char>, needle: Seq<char>, start_pos: int) -> bool {
    if needle.len() == 0 {
        true
    } else if start_pos < 0 || start_pos + needle.len() > haystack.len() {
        false
    } else {
        haystack.subrange(start_pos, start_pos + needle.len()) == needle
    }
}

proof fn lemma_find_substring_at_equiv(haystack: Seq<char>, needle: Seq<char>, pos: int)
    ensures
        find_substring_at(haystack, needle, pos) == substring_matches(haystack, needle, pos)
{
}

proof fn lemma_subrange_prefix(s: Seq<char>, start: int, len: int, prefix: Seq<char>)
    requires
        0 <= start,
        start + len <= s.len(),
        prefix.len() <= len,
    ensures
        s.subrange(start, start + len).subrange(0, prefix.len()) == s.subrange(start, start + prefix.len())
{
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
    /* code modified by LLM (iteration 5): Fixed compilation errors by moving type casts to proof blocks */
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (result[j] == -1 <==> 
                    forall|pos: int| start[j] as int <= pos && pos <= end_pos[j] as int && pos + sub[j]@.len() <= a[j]@.len() ==>
                        !find_substring_at(a[j]@, sub[j]@, pos)) &&
                (result[j] >= 0 ==> 
                    start[j] as int <= result[j] as int && 
                    result[j] as int <= end_pos[j] as int &&
                    result[j] as int + sub[j]@.len() <= a[j]@.len() &&
                    find_substring_at(a[j]@, sub[j]@, result[j] as int) &&
                    forall|pos: int| start[j] as int <= pos && pos < result[j] as int ==> 
                        !find_substring_at(a[j]@, sub[j]@, pos)) &&
                (sub[j]@.len() == 0 ==> result[j] == start[j]) &&
                (start[j] as int + sub[j]@.len() > a[j]@.len() ==> result[j] == -1) &&
                (start[j] > end_pos[j] ==> result[j] == -1)
            }
    {
        if sub[i]@.len() == 0 {
            result.push(start[i]);
        } else {
            proof {
                assert(start[i] >= 0);
                assert(end_pos[i] < a[i]@.len());
            }
            
            if start[i] > end_pos[i] {
                result.push(-1);
            } else {
                proof {
                    let start_int = start[i] as int;
                    let sub_len = sub[i]@.len();
                    let a_len = a[i]@.len();
                    
                    if start_int + sub_len > a_len {
                        assert(start[i] as int + sub[i]@.len() > a[i]@.len());
                    }
                }
                
                let start_plus_sub = start[i] as usize + sub[i].len();
                if start_plus_sub > a[i].len() {
                    result.push(-1);
                } else {
                    let mut pos = start[i];
                    let mut found = -1;
                    
                    while pos <= end_pos[i] {
                        proof {
                            let pos_int = pos as int;
                            let sub_len = sub[i]@.len();
                            let a_len = a[i]@.len();
                            
                            if pos_int + sub_len > a_len {
                                break;
                            }
                        }
                        
                        let pos_plus_sub = pos as usize + sub[i].len();
                        if pos_plus_sub > a[i].len() {
                            break;
                        }
                        
                        if found >= 0 {
                            break;
                        }
                        
                        let mut matches = true;
                        let mut k = 0;
                        
                        while k < sub[i].len()
                            invariant
                                0 <= k <= sub[i].len(),
                                matches == (forall|j: int| 0 <= j < k ==> a[i]@[pos as int + j] == sub[i]@[j]),
                                pos as usize + sub[i].len() <= a[i].len()
                        {
                            if a[i][pos as usize + k] != sub[i][k] {
                                matches = false;
                                break;
                            }
                            k += 1;
                        }
                        
                        if matches {
                            found = pos;
                        } else {
                            pos += 1;
                        }
                    }
                    
                    result.push(found);
                }
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}