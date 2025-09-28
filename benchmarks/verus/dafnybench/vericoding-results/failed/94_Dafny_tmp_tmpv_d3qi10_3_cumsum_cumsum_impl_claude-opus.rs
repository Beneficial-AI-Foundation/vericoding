use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<i32>, i: int) -> int
    recommends 
        0 <= i < a.len(),
    decreases i
{
    if 0 <= i < a.len() {
        a[i] as int + if i == 0 { 0 } else { sum(a, i - 1) }
    } else {
        0
    }
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn cumsum(a: &[i32], b: &mut [i32])
    requires 
        a.len() == old(b).len(),
        a.len() > 0,
    ensures 
        forall|i: int| 0 <= i < a.len() ==> b[i] as int == sum(a@, i),
// </vc-spec>
// <vc-code>
{
    let mut j: usize = 0;
    let mut acc: i32 = 0;
    
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            a.len() == b.len(),
            acc as int == if j == 0 { 0 } else { sum(a@, (j - 1) as int) },
            forall|k: int| 0 <= k < j ==> b[k] as int == sum(a@, k),
        decreases a.len() - j,
    {
        // Update accumulator
        acc = (acc as int + a[j] as int) as i32;
        b[j] = acc;
        
        // Prove the invariant is maintained
        proof {
            assert(sum(a@, j as int) == a@[j as int] as int + if j == 0 { 0 } else { sum(a@, (j - 1) as int) });
            assert(acc as int == sum(a@, j as int));
            assert(b@[j as int] as int == sum(a@, j as int));
        }
        
        j = j + 1;
    }
    
    assert(j == a.len());
    assert(forall|i: int| 0 <= i < a.len() ==> b[i] as int == sum(a@, i));
}
// </vc-code>

fn main() {}

}