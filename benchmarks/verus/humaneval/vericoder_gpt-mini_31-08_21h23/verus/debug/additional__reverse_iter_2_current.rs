use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: nat = a.len();
    let mut res: Vec<i32> = Vec::new();
    res.reserve(n);
    let mut i: nat = 0;
    while i < n
        invariant i <= n;
        invariant res.len() == i;
        invariant forall |j: int| 0 <= j && j < (i as int) ==> res@[j] == a@[(n as int) - 1 - j];
    {
        let val: i32 = a[n - 1 - i];
        res.push(val);
        i = i + 1;
    }
    let result = res;
    proof {
        assert(result.len() == n);
        assert(forall |k: int| 0 <= k && k < result.len() ==> result@[k] == a@[(n as int) - 1 - k]);
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}