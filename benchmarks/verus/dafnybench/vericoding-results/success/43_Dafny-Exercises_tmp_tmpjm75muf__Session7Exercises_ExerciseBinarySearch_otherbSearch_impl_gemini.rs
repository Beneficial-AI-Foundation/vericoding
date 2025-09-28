// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

fn binary_search(v: &Vec<i32>, elem: i32) -> (p: i32)
    requires sorted(v@),
    ensures -1 <= p < v.len(),
            (forall|u: int| 0 <= u <= p ==> v[u] <= elem),
            (forall|w: int| p < w < v.len() ==> v[w] > elem),
{
    assume(false);
    -1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn other_b_search(v: &Vec<i32>, elem: i32) -> (res: (bool, usize))
    requires sorted(v@)
    ensures 
        0 <= res.1 <= v.len(),
        res.0 == v@.contains(elem),
        res.0 ==> res.1 < v.len() && v[res.1 as int] == elem,
        !res.0 ==> forall|u: int| 0 <= u < res.1 ==> v[u] < elem,
        !res.0 ==> forall|w: int| res.1 <= w < v.len() ==> v[w] > elem
// </vc-spec>
// <vc-code>
{
    let mut low: usize = 0;
    let mut high: usize = v.len();
    while low < high
        invariant
            0 <= low <= high <= v.len(),
            sorted(v@),
            forall|i: int| 0 <= i < low as int ==> v@[i] < elem,
            forall|j: int| high as int <= j < v.len() ==> v@[j] > elem,
        decreases high - low
    {
        let mid: usize = low + (high - low) / 2;
        if v[mid] < elem {
            low = mid + 1;
        } else if v[mid] > elem {
            high = mid;
        } else {
            return (true, mid);
        }
    }

    proof {
        assert(low == high);
        assert forall|k: int| 0 <= k < v.len() implies v@[k] != elem by {
            if k < low as int {
                assert(v@[k] < elem);
            } else {
                assert(v@[k] > elem);
            }
        };
        assert(!v@.contains(elem));
    }

    (false, low)
}
// </vc-code>

}
fn main() {}