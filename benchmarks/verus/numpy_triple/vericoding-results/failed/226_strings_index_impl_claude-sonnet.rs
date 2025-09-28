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
    /* code modified by LLM (iteration 5): fixed type casting errors for non-ghost code */
    let mut result: Vec<i8> = Vec::new();
    let mut idx = 0;
    while idx < a.len()
        invariant
            result.len() == idx,
            idx <= a.len(),
            forall|j: int| 0 <= j < idx ==> {
                &&& result@[j] as int >= 0
                &&& start@[j] as int <= result@[j] as int <= end_pos@[j] as int
                &&& result@[j] as int + sub@[j].len() as int <= a@[j].len() as int
            },
        decreases a.len() - idx
    {
        let mut found_idx = start[idx];
        let mut search_pos = start[idx] as usize;
        while search_pos <= end_pos[idx] as usize
            invariant
                start[idx] as int <= found_idx as int <= end_pos[idx] as int,
                search_pos <= end_pos[idx] as usize + 1,
                found_idx as int + sub[idx].len() as int <= a[idx].len() as int,
            decreases end_pos[idx] as usize + 1 - search_pos
        {
            if search_pos + sub[idx].len() as usize <= a[idx].len() as usize {
                let mut match_found = true;
                let mut check_idx = 0usize;
                while check_idx < sub[idx].len() as usize
                    invariant
                        check_idx <= sub[idx].len() as usize,
                        match_found ==> forall|k: int| 0 <= k < check_idx as int ==> a[idx][search_pos + k] == sub[idx][k],
                    decreases sub[idx].len() as usize - check_idx
                {
                    if a[idx][search_pos + check_idx] != sub[idx][check_idx] {
                        match_found = false;
                        break;
                    }
                    check_idx += 1;
                }
                if match_found {
                    found_idx = search_pos as i8;
                    break;
                }
            }
            if search_pos == end_pos[idx] as usize {
                break;
            }
            search_pos += 1;
        }
        result.push(found_idx);
        idx += 1;
    }
    result
}
// </vc-code>

}
fn main() {}