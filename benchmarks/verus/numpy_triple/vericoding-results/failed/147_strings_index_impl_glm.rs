// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 3): fixed compilation error by using usize for indices and adjusted search logic */
{
    let mut result = Vec::new();
    for i in 0..a.len() {
        let s = a[i];
        let pattern = sub[i];
        let low = start[i];
        let high = end_pos[i];
        let max_index = s.len() - pattern.len();

        let low_usize = low as usize;
        let high_usize = high as usize;
        let search_end = if high_usize < max_index { high_usize } else { max_index };

        let mut found_index = search_end as int;
        let mut j = low_usize;
        while j <= search_end {
            let mut match_found = true;
            let mut k: usize = 0;
            while k < pattern.len() {
                if s[j + k] != pattern[k] {
                    match_found = false;
                    break;
                }
                k = k + 1;
            }
            if match_found {
                found_index = j as int;
                break;
            }
            j = j + 1;
        }

        result.push(found_index);
    }
    result
}
// </vc-code>

}
fn main() {}