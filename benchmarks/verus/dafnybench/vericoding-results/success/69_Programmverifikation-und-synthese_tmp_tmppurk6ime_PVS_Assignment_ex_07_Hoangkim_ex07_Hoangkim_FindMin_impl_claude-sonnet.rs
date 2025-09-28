use vstd::prelude::*;

verus! {

//Problem01
//a)

//b)
//Problem04

//Problem02
spec fn sorted(a: Seq<int>) -> bool {
    forall|i: int| 1 <= i < a.len() ==> #[trigger] a[i] >= a[i-1]
}



//Problem03

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_min(a: &[int], lo: usize) -> (minIdx: usize)
    requires 
        a.len() > 0,
        lo < a.len(),
    ensures 
        lo <= minIdx < a.len(),
        forall|x: int| lo <= x < a.len() ==> a[minIdx as int] <= a[x],
// </vc-spec>
// <vc-code>
{
    let mut min_idx = lo;
    let mut i = lo + 1;
    
    while i < a.len()
        invariant
            lo <= min_idx < a.len(),
            lo + 1 <= i <= a.len(),
            forall|x: int| lo <= x < i ==> a[min_idx as int] <= a[x],
        decreases a.len() - i
    {
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i += 1;
    }
    
    min_idx
}
// </vc-code>

fn main() {}

}