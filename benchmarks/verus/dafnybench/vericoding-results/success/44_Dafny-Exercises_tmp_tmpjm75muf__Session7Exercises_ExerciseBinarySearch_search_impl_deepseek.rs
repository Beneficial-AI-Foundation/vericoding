use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

fn binary_search(v: &[int], elem: int) -> (p: i32)
    requires sorted(v@)
    ensures 
        -1 <= p < v@.len() &&
        (forall|u: int| 0 <= u <= p ==> v@[u] <= elem) &&
        (forall|w: int| p < w < v@.len() ==> v@[w] > elem)
{
    assume(false);
    -1
}

// <vc-helpers>
proof fn binary_search_ensures_contains(v: &[int], elem: int, p: i32)
    requires
        sorted(v@),
        -1 <= p < v@.len(),
        forall|u: int| 0 <= u <= p ==> v@[u] <= elem,
        forall|w: int| p < w < v@.len() ==> v@[w] > elem
    ensures
        v@.contains(elem) == (p >= 0 && v@[p as int] == elem)
{
    if p >= 0 {
        assert(v@[p as int] <= elem) by {
            let p_int = p as int;
            assert(0 <= p_int <= p_int);
        }
        if v@[p as int] == elem {
            assert(v@.contains(elem)) by {
                assert(v@[p as int] == elem);
            }
        } else {
            assert(forall|i: int| 0 <= i <= p ==> v@[i] <= elem) by {
                assert(forall|u: int| 0 <= u <= p ==> v@[u] <= elem);
            }
            assert(forall|i: int| 0 <= i <= p ==> v@[i] < elem) by {
                assert(forall|i: int| 0 <= i <= p ==> v@[i] <= elem);
                assert(v@[p as int] == elem || v@[p as int] < elem);
                assert(v@[p as int] != elem);
            }
            assert(forall|i: int| p < i < v@.len() ==> v@[i] > elem);
            assert(!v@.contains(elem)) by {
                assert(forall|i: int| 0 <= i < v@.len() ==> v@[i] != elem);
            }
        }
    } else {
        assert(forall|i: int| 0 <= i < v@.len() ==> v@[i] > elem) by {
            assert(p == -1);
            assert(forall|w: int| p < w < v@.len() ==> v@[w] > elem);
            assert(-1 < 0);
        }
        assert(!v@.contains(elem));
    }
}
// </vc-helpers>

// <vc-spec>
fn search(v: &[int], elem: int) -> (b: bool)
    requires sorted(v@)
    ensures b == v@.contains(elem)
    //Implement by calling binary search function
// </vc-spec>
// <vc-code>
{
    let p = binary_search(v, elem);
    proof {
        binary_search_ensures_contains(v, elem, p);
    }
    p >= 0 && v[p as usize] == elem
}
// </vc-code>

fn main() {
    //Recursive binary search
}

}