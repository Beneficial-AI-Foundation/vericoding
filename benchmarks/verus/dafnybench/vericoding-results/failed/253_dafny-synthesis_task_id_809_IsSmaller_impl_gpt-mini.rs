use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
fn is_smaller(a: Seq<int>, b: Seq<int>) -> (result: bool)
    requires 
        a.len() == b.len(),
    ensures 
        result <==> forall|i: int| 0 <= i < a.len() ==> a[i] > b[i],
        !result <==> exists|i: int| 0 <= i < a.len() && a[i] <= b[i],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: int = 0;
    let mut r: bool = true;
    while i < n {
        invariant 0 <= i && i <= n;
        invariant r ==> (forall|j: int| 0 <= j && j < i ==> a@[j] > b@[j]);
        invariant !r ==> (exists|j: int| 0 <= j && j < i && a@[j] <= b@[j]);
        decreases n - i;
        if a@[i] > b@[i] {
            i = i + 1;
        } else {
            let k = i;
            r = false;
            i = i + 1;
            proof {
                assert(0 <= k && k < i);
                assert(a@[k] <= b@[k]);
                assert(exists|j: int| 0 <= j && j < i && a@[j] <= b@[j]);
            }
        }
    }
    result = r;
    proof {
        assert(i == n);
        if result {
            assert(forall|j: int| 0 <= j && j < i ==> a@[j] > b@[j]);
            assert(forall|j: int| 0 <= j && j < n ==> a@[j] > b@[j]);
        } else {
            assert(exists|j: int| 0 <= j && j < i && a@[j] <= b@[j]);
            assert(exists|j: int| 0 <= j && j < n && a@[j] <= b@[j]);
        }
    }
}
// </vc-code>

fn main() {}

}