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
proof fn binary_search_implies_contains(v: Seq<int>, elem: int, p: i32)
    requires
        sorted(v),
        -1 <= p < v.len(),
        forall|u: int| 0 <= u <= p ==> v[u] <= elem,
        forall|w: int| p < w < v.len() ==> v[w] > elem,
    ensures
        v.contains(elem) <==> (p >= 0 && v[p as int] == elem)
{
    if p >= 0 {
        let idx = p as int;
        if v.contains(elem) {
            let i = choose|i| 0<=i<v.len() && v[i]==elem;
            assert(v[i]==elem);
            if i > p {
                assert(v[i] > elem);
                assert(false);
            }
            assert(i <= p);
            assert(v[i] <= v[idx]);
            assert(v[idx] >= elem);
            assert(v[idx] <= elem);
            assert(v[idx] == elem);
        }
        if v[idx]==elem {
            assert(v.contains(elem));
        }
    } else {
        assert(!v.contains(elem));
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
        binary_search_implies_contains(v@, elem, p);
    }
    if p >= 0 {
        let idx = p as usize;
        v[idx] == elem
    } else {
        false
    }
}
// </vc-code>

fn main() {
    //Recursive binary search
}

}