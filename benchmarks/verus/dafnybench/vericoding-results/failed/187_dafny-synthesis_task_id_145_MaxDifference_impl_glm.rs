use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_difference(a: &[i32]) -> (diff: i32)
    requires a.len() > 1
    ensures forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
    let n = a.len() as int;
    let mut min_val = a[0];
    let mut max_val = a[0];
    let mut i = 1 as int;
    while (i < n)
        invariant 1 <= i && i <= n,
        invariant {
            forall|k: int| 0 <= k < i ==> min_val <= a@[k]
        },
        invariant {
            forall|k: int| 0 <= k < i ==> a@[k] <= max_val
        }
    {
        let x = a[i as usize];
        if x < min_val {
            min_val = x;
        }
        if x > max_val {
            max_val = x;
        }
        i += 1;
    }
    let diff = max_val - min_val;
    proof {
        assert(forall|k: int| 0<=k<n ==> min_val <= a@[k]);
        assert(forall|k: int| 0<=k<n ==> a@[k] <= max_val);

        assert forall|i: int, j: int| 0<=i<n && 0<=j<n {
            a@[i] - a@[j] <= diff
        } by {
            assert(a@[i] <= max_val);
            assert(min_val <= a@[j]);
            assert(a@[i] - a@[j] <= max_val - a@[j]);
            assert(max_val - a@[j] <= max_val - min_val);
        }
    }
    diff
}
// </vc-code>

fn main() {
}

}