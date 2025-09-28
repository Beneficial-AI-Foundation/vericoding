use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// No helper changes needed.
 
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn index_wise_addition(a: Seq<Seq<int>>, b: Seq<Seq<int>>) -> (result: Seq<Seq<int>>)
    requires 
        a.len() > 0 && b.len() > 0,
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i].len() == b[i].len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == a[i].len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] == a[i][j] + b[i][j],
// </vc-spec>
// <vc-code>
{
    let mut outer: Vec<Seq<int>> = Vec::new();
    let mut i: nat = 0;
    while i < a.len()
        invariant i <= a.len();
        invariant Seq::from(outer).len() == i;
        invariant forall|k: nat| k < i ==> Seq::from(outer)@[(k as int)].len() == a@[(k as int)].len();
        invariant forall|k: nat, t: nat| k < i && t < Seq::from(outer)@[(k as int)].len() ==>
            Seq::from(outer)@[(k as int)]@[(t as int)] == a@[(k as int)]@[(t as int)] + b@[(k as int)]@[(t as int)];
    {
        let ai = a@[(i as int)];
        let bi = b@[(i as int)];
        let mut inner: Vec<int> = Vec::new();
        let mut j: nat = 0;
        while j < ai.len()
            invariant j <= ai.len();
            invariant Seq::from(inner).len() == j;
            invariant forall|t: nat| t < j ==> Seq::from(inner)@[(t as int)] == ai@[(t as int)] + bi@[(t as int)];
        {
            let old_j = j;
            let v = ai@[(old_j as int)] + bi@[(old_j as int)];
            inner.push(v);
            j = old_j + 1;
            // establish that the newly pushed element is as expected
            assert(Seq::from(inner)@[(old_j as int)] == ai@[(old_j as int)] + bi@[(old_j as int)]);
        }
        let s_inner = Seq::from(inner);
        outer.push(s_inner);
        i = i + 1;
    }
    Seq::from(outer)
}
// </vc-code>

fn main() {}

}