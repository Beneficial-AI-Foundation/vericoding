// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_pair_sum_to_zero(l: Seq<int>) -> bool {
    exists|i: int, j: int| 0 <= i < j < l.len() && l[i] + l[j] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn pairs_sum_to_zero(l: Vec<i8>) -> (result: bool)
    ensures result == has_pair_sum_to_zero(l@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by using usize for indexing exec vector and int for spec invariants */
{
    let len = l.len();
    let mut i_usize = 0;
    while i_usize < len
        invariant
            i_usize <= len,
            forall|k: int, m: int| 0 <= k < m < (i_usize as int) ==> (l@[k] as int) + (l@[m] as int) != 0,
        decreases len - i_usize
    {
        let mut j_usize = i_usize + 1;
        while j_usize < len
            invariant
                j_usize <= len,
                j_usize > i_usize,
                forall|k: int| 0 <= k < (j_usize as int) && k != (i_usize as int) ==> (l@[k] as int) + (l@[(i_usize as int)] as int) != 0,
            decreases len - j_usize
        {
            if (l[i_usize] as int) + (l[j_usize] as int) == 0 {
                return true;
            }
            j_usize = j_usize + 1;
        }
        i_usize = i_usize + 1;
    }
    false
}
// </vc-code>


}

fn main() {}