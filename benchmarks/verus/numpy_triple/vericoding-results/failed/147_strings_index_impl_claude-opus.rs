// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix int usage in exec function */
spec fn substring_matches(a: Seq<char>, sub: Seq<char>, pos: int) -> bool {
    pos >= 0 && pos + sub.len() as int <= a.len() as int &&
    forall|j: int| 0 <= j < sub.len() as int ==> a[pos + j] == sub[j]
}

fn find_substring_exec(a: &Vec<char>, sub: &Vec<char>, start: usize, end_pos: usize) -> (result: usize)
    requires
        start <= end_pos,
        end_pos <= a.len(),
        sub.len() > 0,
    ensures
        result >= start,
        result <= end_pos,
        result + sub.len() <= a.len() + 1,
        (result < end_pos && result + sub.len() <= a.len()) ==> substring_matches(a@, sub@, result as int)
{
    let mut i: usize = start;
    while i < end_pos && i + sub.len() <= a.len()
        invariant
            start <= i <= end_pos,
            i + sub.len() <= a.len() + 1,
            forall|k: int| start as int <= k < i as int ==> !substring_matches(a@, sub@, k)
    {
        let mut found = true;
        let mut j: usize = 0;
        while j < sub.len()
            invariant
                j <= sub.len(),
                found == (forall|k: int| 0 <= k < j as int ==> a@[(i as int) + k] == sub@[k])
        {
            if a[i + j] != sub[j] {
                found = false;
                break;
            }
            j = j + 1;
        }
        if found {
            return i;
        }
        i = i + 1;
    }
    end_pos
}

fn seq_to_vec(s: &Seq<char>) -> (v: Vec<char>)
    ensures
        v.len() == s.len(),
        v@ == s
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v.len() == i,
            forall|j: int| 0 <= j < i as int ==> v@[j] == s[j]
    {
        v.push(s[i as usize]);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn index(a: Vec<Seq<char>>, sub: Vec<Seq<char>>, start: Vec<int>, end_pos: Vec<int>) -> (result: Vec<int>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& start[i] >= 0 
            &&& start[i] <= end_pos[i]
            &&& end_pos[i] <= a[i].len() as int
            &&& sub[i].len() > 0
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& result[i] >= 0
            &&& start[i] <= result[i] <= end_pos[i]
            &&& result[i] + sub[i].len() as int <= a[i].len() as int
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Convert usize to int properly */
{
    let mut result: Vec<int> = Vec::new();
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|k: int| 0 <= k < idx as int ==> {
                &&& result[k] >= 0
                &&& start[k] <= result[k] <= end_pos[k]
                &&& result[k] + sub[k].len() as int <= a[k].len() as int
            }
    {
        let a_seq = &a[idx];
        let sub_seq = &sub[idx];
        let start_pos = start[idx];
        let end = end_pos[idx];
        
        let a_vec = seq_to_vec(a_seq);
        let sub_vec = seq_to_vec(sub_seq);
        
        let found_idx_usize = find_substring_exec(&a_vec, &sub_vec, start_pos as usize, end as usize);
        let found_idx: int = found_idx_usize as int;
        result.push(found_idx);
        idx = idx + 1;
    }
    result
}
// </vc-code>

}
fn main() {}