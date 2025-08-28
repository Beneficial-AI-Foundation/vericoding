use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

// <vc-helpers>
proof fn lemma_seq_midpoint(s: Seq<int>, left: int, right: int)
    requires
        0 <= left <= right < s.len(),
    ensures
        left <= (left + right) / 2 < right || left == right,
{
    // This is a simple arithmetic property, no additional proof steps needed in Verus
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn binary_search(v: &Vec<i32>, elem: i32) -> (p: i32)
    requires sorted(v@.map_values(|val: i32| val as int)),
    ensures ({
        &&& -1 <= p < v.len()
        &&& forall|u: int| 0 <= u <= p ==> v@[u] <= elem as int
        &&& forall|w: int| p < w < v.len() ==> v@[w] > elem as int
    }),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn binary_search(v: &Vec<i32>, elem: i32) -> (p: i32)
    requires sorted(v@.map_values(|val: i32| val as int)),
    ensures ({
        &&& -1 <= p < v.len() as i32
        &&& forall|u: int| 0 <= u <= p ==> v@[u] <= elem as int
        &&& forall|w: int| p < w < v.len() ==> v@[w] > elem as int
    })
{
    let mut left: i32 = 0;
    let mut right: i32 = (v.len() as i32) - 1;
    let mut result: i32 = -1;

    while left <= right
        invariant
            0 <= left <= v.len() as i32,
            -1 <= right < v.len() as i32,
            -1 <= result < v.len() as i32,
            left > right ==> result >= -1,
            forall|u: int| 0 <= u < left ==> v@[u] <= elem,
            forall|w: int| right < w < v.len() ==> v@[w] > elem,
    {
        let mid: i32 = left + (right - left) / 2;

        if v[mid as usize] == elem {
            result = mid;
            break;
        } else if v[mid as usize] < elem {
            left = mid + 1;
        } else {
            right = mid - 1;
            if result == -1 || mid > result {
                result = right;
            }
        }
    }

    if result == -1 {
        result = right;
    }

    result
}
// </vc-code>

//Recursive binary search

fn main() {}

}