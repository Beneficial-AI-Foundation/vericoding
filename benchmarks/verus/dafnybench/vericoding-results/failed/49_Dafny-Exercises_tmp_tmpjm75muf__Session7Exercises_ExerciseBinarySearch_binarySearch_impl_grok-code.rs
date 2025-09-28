use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

// <vc-helpers>
spec fn is_insertion_point(v: Seq<int>, elem: int, p: int) -> bool {
    &&& -1 <= p < v.len() as int
    &&& forall|u: int| 0 <= u <= p ==> v[u] <= elem
    &&& forall|w: int| #[trigger] v[w] > elem ==> p < w && w < v.len() as int
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
    let ghost elem_g: int = elem as int;
    let ghost v_g: Seq<int> = v@.map_values(|a: i32| a as int);
    if v.len() == 0 {
        return -1;
    }
    let mut low: usize = 0;
    let mut high: usize = v.len();
    while low < high
        invariant
            0 <= low <= high <= v@.len(),
            forall|i: usize| i < low ==> v_g[i] < elem_g,
            forall|i: usize| high <= i < v@.len() ==> v_g[i] >= elem_g,
    {
        let mid = low + (high - low) / 2;
        if v_g[mid] < elem_g {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    let p = low as i32 - 1;
    assert(is_insertion_point(v_g, elem_g, p as int));
    p
}
// </vc-code>

//Recursive binary search

fn main() {}

}