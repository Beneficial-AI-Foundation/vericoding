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
proof fn lemma_sum_base(a: Seq<i32>)
    requires
        a.len() > 0,
    ensures
        sum(a, 0) == a@[0] as int
{
    assert(0 <= 0 < a.len());
    assert(sum(a, 0) == a[0] as int + 0);
    assert(sum(a, 0) == a@[0] as int);
}

proof fn lemma_sum_step(a:
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
proof fn lemma_sum_base(a: Seq<i32>)
    requires
        a.len() > 0,
    ensures
        sum(a, 0) == a@[0] as int
{
    assert(0 <= 0 < a.len());
    assert(sum(a, 0) == a[0] as int + 0);
    assert(sum(a, 0) == a@[0] as int);
}

proof fn lemma_sum_step(a:
// </vc-code>

fn main() {}

}