use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

// <vc-helpers>
// No helpers needed for this example.
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
    let s: Seq<int> = v@.map_values(|val: i32| val as int);
    let n: int = v.len() as int;

    let mut lo: int = -1;
    let mut hi: int = n - 1;

    while lo < hi
        invariant -1 <= lo && lo < n
        invariant -1 <= hi && hi < n
        invariant lo <= hi
        invariant forall|u: int| 0 <= u <= lo ==> s@[u] <= elem as int
        invariant forall|w: int| hi < w < n ==> s@[w] > elem as int
        decreases hi - lo
    {
        let mid: int = lo + (hi - lo + 1) / 2;
        // mid is in (lo..=hi]
        assert(lo < mid && mid <= hi);

        if s@[mid] <= elem as int {
            // show that for all u with 0 <= u <= mid, s[u] <= elem
            proof {
                // sorted(s) is available from the precondition
                assert(sorted(s));
                // For any u with 0 <= u <= mid, we have s[u] <= s[mid] by sortedness,
                // and s[mid] <= elem, hence s[u] <= elem.
                assert(forall|u: int| 0 <= u <= mid ==> s@[u] <= s@[mid]);
                assert(s@[mid] <= elem as int);
                assert(forall|u: int| 0 <= u <= mid ==> s@[u] <= elem as int);
            }
            lo = mid;
        } else {
            // s[mid] > elem, so set hi = mid - 1 and prove the upper invariant
            proof {
                assert(sorted(s));
                // For any w with mid <= w < n, s[w] >= s[mid] by sortedness, so s[w] > elem.
                assert(forall|w: int| mid <= w < n ==> s@[w] >= s@[mid]);
                assert(s@[mid] > elem as int);
                assert(forall|w: int| mid <= w < n ==> s@[w] > elem as int);
                // New hi = mid - 1, so any w with new_hi < w < n satisfies w >= mid, thus s[w] > elem.
                assert(forall|w: int| mid - 1 < w < n ==> s@[w] > elem as int);
            }
            hi = mid - 1;
        }
    }

    lo as i32
}
// </vc-code>

//Recursive binary search

fn main() {}

}