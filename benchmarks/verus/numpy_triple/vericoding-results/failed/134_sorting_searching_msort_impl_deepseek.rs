// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed nat usage in exec context by converting to usize */
fn merge_sorted(a: Seq<i32>, b: Seq<i32>) -> (result: Seq<i32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result.to_multiset() =~= a.to_multiset().add(b.to_multiset())
{
    if a.len() == 0 {
        b
    } else if b.len() == 0 {
        a
    } else {
        if a@[0] <= b@[0] {
            proof { ghost_convert_length(a.len()); }
            Seq::new(1, |i: nat| a@[i]).concat(merge_sorted(a.subrange(1, a.len() as usize), b))
        } else {
            proof { ghost_convert_length(b.len()); }
            Seq::new(1, |i: nat| b@[i]).concat(merge_sorted(a, b.subrange(1, b.len() as usize)))
        }
    }
}

proof fn merge_sorted_decreases(a: Seq<i32>, b: Seq<i32>)
    decreases a.len() + b.len()
{
}

spec fn ghost_int(n: nat) -> int { n as int }

proof fn ghost_convert_length(n: nat)
    ensures n as int == ghost_int(n)
{
}
// </vc-helpers>

// <vc-spec>
fn msort(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result@.to_multiset() =~= a@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed implementation to use proper merge_sorted helper */
{
    if a.len() <= 1 {
        a
    } else {
        let mid: usize = a.len() / 2;
        proof { 
            ghost_convert_length(mid as nat); 
            ghost_convert_length(a.len() as nat);
        }
        let left = msort(a.slice_to(mid));
        let right = msort(a.slice_from(mid));
        
        let merged_seq = merge_sorted(left@, right@);
        Vec::from_seq(merged_seq)
    }
}
// </vc-code>

}
fn main() {}