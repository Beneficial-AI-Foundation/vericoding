use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

// <vc-helpers>
spec fn sorted_between(s: Seq<int>, start: int, end: int) -> bool {
    forall|u: int, w: int| start <= u < w < end ==> s[u] <= s[w]
}

proof fn binary_search_helper_proof(v: Vec<i32>, elem: i32, left: int, right: int, mid: int)
    requires
        sorted_between(v@.map_values(|val: i32| val as int), left, right),
        left >= 0,
        right <= v.len() as int,
        left <= mid < right,
    ensures
        (forall|u: int| left <= u <= mid ==> v@[u as usize] <= elem as int),
        (forall|w: int| mid < w < right ==> v@[w as usize] > elem as int),
{
    assert(forall|u: int, w: int| left <= u < w < right ==> v@[u as usize] <= v@[w as usize]);
    assert(forall|u: int| left <= u <= mid ==> v@[u as usize] <= v@[mid as usize]);
    assert(v@[mid as usize] <= elem as int);
}

spec fn binary_search_inv(v: Vec<i32>, elem: i32, left: int, right: int) -> bool {
    &&& 0 <= left <= right <= v.len() as int
    &&& sorted_between(v@.map_values(|val: i32| val as int), left, right)
    &&& forall|u: int| 0 <= u < left ==> v@[u as usize] <= elem as int
    &&& forall|w: int| right <= w < v.len() as int ==> v@[w as usize] > elem as int
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
    let mut left: usize = 0;
    let mut right: usize = v.len();
    let v_copy = v.clone();
    
    while left < right
        invariant
            binary_search_inv(v_copy, elem, left as int, right as int),
        decreases right - left
    {
        assert(left < right);
        let mid = left + (right - left) / 2;
        assert(mid >= left && mid < right);
        
        if v[mid] <= elem {
            proof {
                assert(forall|u: int| 0 <= u < left as int ==> v_copy@[u as usize] <= elem as int);
                assert(forall|u: int| left as int <= u <= mid as int ==> v_copy@[u as usize] <= elem as int);
                assert(sorted_between(v_copy@.map_values(|val: i32| val as int), left as int, right as int));
                assert(forall|w: int| right as int <= w < v.len() as int ==> v_copy@[w as usize] > elem as int);
            }
            left = mid + 1;
        } else {
            proof {
                assert(forall|w: int| right as int <= w < v.len() as int ==> v_copy@[w as usize] > elem as int);
                assert(forall|w: int| mid as int < w < right as int ==> v_copy@[w as usize] > elem as int);
                assert(sorted_between(v_copy@.map_values(|val: i32| val as int), left as int, right as int));
                assert(forall|u: int| 0 <= u < left as int ==> v_copy@[u as usize] <= elem as int);
            }
            right = mid;
        }
    }
    
    proof {
        assert(left >= right);
        binary_search_helper_proof(v_copy, elem, 0, v.len() as int, (left - 1) as int);
    }
    
    let p = if left > 0 { (left as i32) - 1 } else { -1 };
    p
}
// </vc-code>

//Recursive binary search

fn main() {}

}