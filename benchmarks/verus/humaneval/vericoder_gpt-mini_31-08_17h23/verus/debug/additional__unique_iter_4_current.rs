use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper functions needed for this proof; section left intentionally empty.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: int = a.len() as int;
    if n == 0 {
        return vec![];
    }

    let mut res: Vec<i32> = vec![a[0]];
    let mut i: int = 1;

    while i < n
        invariant 1 <= i && i <= n;
        invariant (res.len() as int) >= 1;
        invariant forall |u: int, v: int|
            #![trigger res@[u], res@[v]]
            0 <= u && u < v && v < (res.len() as int) ==> res@[u] < res@[v];
        invariant forall |j: int|
            #![trigger res]
            0 <= j && j < i ==> exists |t: int| 0 <= t && t < (res.len() as int) && res@[t] == a[j];
        invariant forall |t: int|
            #![trigger res@[t]]
            0 <= t && t < (res.len() as int) ==> exists |p: int| 0 <= p && p < i && res@[t] == a[p]
    {
        if a[i] != res@[(res.len() as int) - 1] {
            res.push(a[i]);
        }
        i += 1;
    }

    // After loop, i == n, invariants give that res is strictly increasing.
    res
    // impl-end
}
// </vc-code>

fn main() {}
}