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
spec fn sum_seq(a: Seq<i32>, i: int) -> int
    recommends 
        0 <= i < a.len(),
    decreases i
{
    if 0 <= i < a.len() {
        a[i] as int + if i == 0 { 0 } else { sum_seq(a, i - 1) }
    } else {
        0
    }
}

proof fn sum_initial(a: Seq<i32>)
    requires
        a.len() > 0,
    ensures
        sum_seq(a, 0) == a[0] as int,
{
}

proof fn sum_recursive(a: Seq<i32>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        sum_seq(a, i) == if i == 0 { a[0] as int } else { sum_seq(a, i - 1) + a[i] as int },
    decreases i
{
    if i > 0 {
        sum_recursive(a, i - 1);
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
    assert(n > 0);
    
    b[0] = a[0];
    proof {
        sum_initial(a@);
        assert(b[0] as int == sum_seq(a@, 0));
    }
    
    let mut k: usize = 1;
    while k < n
        invariant
            k <= n,
            forall|i: nat| i < k ==> b[i] as int == sum_seq(a@, i as int),
        decreases n - k
    {
        let k_int: int = k as int;  // This is now in proof context
        b[k] = b[k - 1] + a[k];
        proof {
            sum_recursive(a@, k_int);
            assert(sum_seq(a@, k_int) == sum_seq(a@, (k_int - 1)) + a@[k_int] as int);
            assert(b[k] as int == b[k - 1] as int + a[k] as int);
            assert(b[k] as int == sum_seq(a@, k_int));
        }
        k = k + 1;
    }
    
    proof {
        assert forall|i: int| 0 <= i < n implies b[i] as int == sum_seq(a@, i) by {
            if i < k as int {
                assert(b[i as usize] as int == sum_seq(a@, i));
            }
        };
    }
}
// </vc-code>

fn main() {}

}