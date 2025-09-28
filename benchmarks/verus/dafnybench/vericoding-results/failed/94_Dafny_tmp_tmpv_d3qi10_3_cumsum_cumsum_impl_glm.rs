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

proof fn lemma_sum_add(a: Seq<i32>, i: int)
    requires
        0 <= i + 1 < a.len(),
    ensures
        sum(a, i + 1) == a[i + 1] as int + sum(a, i)
{
    if i + 1 == 0 {
    } else if i == 0 {
    } else {
        lemma_sum_add(a, i - 1);
    }
}

proof fn lemma_sum_index(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        sum(a, i) == a[i] as int + sum(a, i - 1),
{
    if i == 0 {
    } else {
        lemma_sum_index(a, i - 1);
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
    let n = a.len();
    b[0] = a[0];
    proof {
        assert(a@[0] as int == sum(a@, 0));
    }
    for i in 1..n
        invariant 
            1 <= i <= n,
            forall|j: int| 0 <= j < (i as int) ==> b[j] as int == #[trigger] sum(a@, j),
    {
        proof {
            lemma_sum_add(a@, i as int - 1);
            assert(b[i-1] as int == sum(a@, (i as int) - 1));
            assert(a@[i as int] as int + sum(a@, (i as int) - 1) == sum(a@, i as int));
        }
        b[i] = b[i-1] + a[i];
    }
}
// </vc-code>

fn main() {}

}