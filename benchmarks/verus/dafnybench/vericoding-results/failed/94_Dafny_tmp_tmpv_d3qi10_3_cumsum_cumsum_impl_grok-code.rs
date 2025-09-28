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
fn sum(a: Seq<i32>, i: int) -> int
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
    let mut running_sum: i32 = 0;
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall |k: int| #[trigger sum(a@, k)] 0 <= k < i ==> b@[k] as int == sum(a@, k),
            running_sum as int == if i == 0 { 0 } else { sum(a@, i - 1) },
        decreases a.len() - i
    {
        b[i] = running_sum + a[i];
        proof {
            assert(b@[i] == running_sum as int + a[i] as int);
        }
        running_sum = running_sum + a[i];
        proof {
            reveal(sum);
            assert(running_sum as int == sum(a@, i));
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}