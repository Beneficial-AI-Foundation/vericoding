use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn pointwise_sum(a: &Vec<i32>, b: &Vec<i32>) -> Seq<i32>
    requires a.len() == b.len(),
{
    let len = a.len();
    Seq::new(|i: int| a@[i] + b@[i], len)
}
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] + b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut c = Vec::new();
    for i in 0..n
        invariant
            0 <= i <= n,
            c.len() == i,
            a.len() == n,
            b.len() == n,
            c@ == pointwise_sum(&a, &b).take(i as int),
    {
        c.push(a@[i] + b@[i]);
        assert(c@ == pointwise_sum(&a, &b).take((i+1) as int));
    }
    c
}
// </vc-code>

fn main() {}

}