use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

// <vc-helpers>
proof fn lemma_sorted_implies_greater_from_index(s: Seq<int>, i: int, e: int)
    requires
        sorted(s),
        0 <= i < s.len(),
        s[i] > e,
    ensures
        forall|j: int| i <= j < s.len() ==> s[j] > e
{
    assert forall|j: int| i <= j < s.len() implies s[j] > e by {
        if i < j {
            assert(s[i] <= s[j]);
        }
        assert(s[j] >= s[i]);
        assert(s[j] > e);
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search(v: &Vec<i32>, elem: i32) -> (p: i32)
    requires sorted(v@.map_values(|val: i32| val as int)),
    ensures ({
        &&& -1 <= p < v.len()
        &&& forall|u: int| 0 <= u <= p ==> v@[u] <= elem as int
        &&& forall|w: int| p < w < v.len() ==> v@[w] > elem as int
    }),
// </vc-spec>
// <vc-code>
{
    let mut low: i32 = 0;
    let mut high: i32 = v.len() as i32;

    while low < high
        invariant
            0 <= low <= high <= v.len() as int,
            forall|i: int| 0 <= i < low ==> (v@[i] as int) <= (elem as int),
            forall|i: int| high <= i < v.len() as int ==> (v@[i] as int) > (elem as int)
        decreases (high - low)
    {
        let mid: i32 = (low + high) / 2;
        if v[mid as usize] <= elem {
            let old_low = low;
            low = mid + 1;
            proof {
                let s = v@.map_values(|x: i32| x as int);
                assert forall|i: int| 0<=i<low implies s[i] <= elem as int by {
                    if i < old_low {
                    } else {
                        assert(s[i] <= s[mid as int]);
                        assert(s[mid as int] <= elem as int);
                    }
                }
            }
        } else {
            proof {
                let s = v@.map_values(|x: i32| x as int);
                lemma_sorted_implies_greater_from_index(s, mid as int, elem as int);
            }
            high = mid;
        }
    }
    low - 1
}
// </vc-code>

//Recursive binary search

fn main() {}

}