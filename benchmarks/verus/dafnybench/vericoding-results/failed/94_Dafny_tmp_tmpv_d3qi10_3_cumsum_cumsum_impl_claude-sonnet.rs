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
proof fn sum_property(a: Seq<i32>, i: int)
    requires 0 <= i < a.len()
    ensures sum(a, i) == a[i] as int + sum(a, i - 1)
{
}

proof fn sum_base_case(a: Seq<i32>)
    requires a.len() > 0
    ensures sum(a, 0) == a[0] as int
{
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
    b[0] = a[0];
    assert(sum(a@, 0) == a@[0] as int);
    
    let mut j = 1;
    while j < a.len()
        invariant
            1 <= j <= a.len(),
            a.len() == b.len(),
            forall|k: int| 0 <= k < j ==> b[k] as int == sum(a@, k),
        decreases
            a.len() - j,
    {
        b[j] = a[j] + b[j - 1];
        
        proof {
            sum_property(a@, j as int);
            assert(sum(a@, j as int) == a@[j as int] as int + sum(a@, j as int - 1));
            assert(b@[j as int - 1] as int == sum(a@, j as int - 1));
            assert(b@[j as int] as int == a@[j as int] as int + b@[j as int - 1] as int);
            assert(b@[j as int] as int == a@[j as int] as int + sum(a@, j as int - 1));
            assert(b@[j as int] as int == sum(a@, j as int));
        }
        
        j = j + 1;
    }
}
// </vc-code>

fn main() {}

}