use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn div_proof(x: int, y: int) 
    requires y != 0,
    ensures x / y == x / y,
{
}

spec fn div_spec(a: Seq<int>, b: Seq<int>, i: int) -> int
    recommends 0 <= i < b.len(),
    recommends b[i] != 0,
{
    a[i] / b[i]
}
// </vc-helpers>

// <vc-spec>
fn element_wise_divide(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] / b[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Seq::<int>::empty();
    let mut n: nat = 0;
    while n < a.len()
        invariant
            0 <= n <= a.len(),
            result.len() == n,
            forall|i: nat| i < n ==> result[i] == a[i] / b[i],
    {
        result = result.add(a[n as int] / b[n as int]);
        proof {
            div_proof(a[n as int], b[n as int]);
        }
        n = n + 1;
    }
    result
}
// </vc-code>

fn main() {
}

}