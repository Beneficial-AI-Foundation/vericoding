use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add_lists(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
{
    proof {
        let n: nat = a.len();
        let mut result = Seq::<int>::new(n, |i: int| 0);
        let mut i: nat = 0;
        while i < n
            invariant
                0 <= i <= n,
                result.len() == a.len(),
                forall|k: int| 0 <= k < i ==> result@[k] == a@[k] + b@[k],
        {
            result = result.update(i, a@[i] + b@[i]);
            i = i + 1;
        }
        result
    }
}
// </vc-code>

fn main() {}

}