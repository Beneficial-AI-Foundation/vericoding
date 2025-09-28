// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn index(a: Vec<Seq<char>>, sub: Vec<Seq<char>>, start: Vec<i8>, end_pos: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& start[i] as int >= 0 
            &&& start[i] as int <= end_pos[i] as int
            &&& end_pos[i] as int <= a[i].len() as int
            &&& sub[i].len() > 0
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& result[i] as int >= 0
            &&& start[i] as int <= result[i] as int <= end_pos[i] as int
            &&& result[i] as int + sub[i].len() as int <= a[i].len() as int
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed Seq access and type conversions */
    let mut result: Vec<i8> = Vec::new();
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            a.len() == sub.len(),
            sub.len() == start.len(),
            start.len() == end_pos.len(),
            forall|i: int| 0 <= i < a.len() ==> {
                &&& start[i] as int >= 0
                &&& start[i] as int <= end_pos[i] as int
                &&& end_pos[i] as int <= a[i].len() as int
                &&& sub[i].len() > 0
            },
            forall|i: int| 0 <= i < result.len() ==> {
                &&& result[i] as int >= 0
                &&& start[i] as int <= result[i] as int <= end_pos[i] as int
                &&& result[i] as int + sub[i].len() as int <= a[i].len() as int
            }
    {
        let curr_a = &a[idx];
        let curr_sub = &sub[idx];
        let curr_start = start[idx];
        let curr_end = end_pos[idx];
        
        let mut pos = curr_start;
        let mut found = false;
        
        let sub_len_usize: usize = curr_sub.len();
        let sub_len = sub_len_usize as i8;
        while pos <= curr_end - sub_len && !found
            invariant
                curr_start as int <= pos as int,
                pos as int <= curr_end as int + 1,
                curr_start as int >= 0,
                curr_start as int <= curr_end as int,
                curr_end as int <= curr_a.len() as int,
                curr_sub.len() > 0,
                sub_len == curr_sub.len() as i8,
                !found ==> forall|j: int| curr_start as int <= j < pos as int ==> {
                    j + curr_sub.len() as int <= curr_a.len() as int ==> {
                        exists|k: int| 0 <= k < curr_sub.len() as int && curr_a[j + k] != curr_sub[k]
                    }
                }
        {
            let a_len_usize: usize = curr_a.len();
            let a_len = a_len_usize as i8;
            if pos + sub_len <= a_len {
                let mut matches = true;
                let mut k: usize = 0;
                
                while k < sub_len_usize && matches
                    invariant
                        k <= curr_sub.len(),
                        matches ==> forall|j: int| 0 <= j < k as int ==> curr_a[pos as int + j] == curr_sub[j],
                        !matches ==> exists|j: int| 0 <= j < k as int && curr_a[pos as int + j] != curr_sub[j]
                {
                    let pos_k = (pos as usize) + k;
                    proof {
                        assert(curr_a[pos_k as int] == curr_a[pos as int + k as int]);
                    }
                    if curr_a.index(pos_k) != curr_sub.index(k) {
                        matches = false;
                    }
                    k = k + 1;
                }
                
                if matches {
                    found = true;
                    result.push(pos);
                }
            }
            
            if !found {
                pos = pos + 1;
            }
        }
        
        if !found {
            result.push(curr_end);
        }
        
        idx = idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}