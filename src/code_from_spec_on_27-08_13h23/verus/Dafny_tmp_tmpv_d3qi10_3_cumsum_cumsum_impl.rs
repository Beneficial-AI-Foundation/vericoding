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

proof fn sum_non_negative(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len(),
        forall|k: int| 0 <= k <= i ==> a[k] >= 0,
    ensures
        sum(a, i) >= 0,
    decreases i
{
    if i > 0 {
        sum_non_negative(a, i - 1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn cumsum(a: &[i32], b: &mut [i32])
    requires 
        a.len() == old(b).len(),
        a.len() > 0,
    ensures 
        forall|i: int| 0 <= i < a.len() ==> b[i] as int == sum(a@, i),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn cumsum(a: &[i32], b: &mut [i32])
    requires 
        a.len() == old(b).len(),
        a.len() > 0,
    ensures 
        forall|i: int| 0 <= i < a.len() ==> b[i] as int == sum(a@, i),
{
    let mut sum_so_far: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i as int ==> b[k] as int == sum(a@, k),
            sum_so_far as int == if i == 0 { 0 } else { sum(a@, i as int - 1) },
    {
        sum_so_far = sum_so_far + a[i];
        b[i] = sum_so_far;
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}