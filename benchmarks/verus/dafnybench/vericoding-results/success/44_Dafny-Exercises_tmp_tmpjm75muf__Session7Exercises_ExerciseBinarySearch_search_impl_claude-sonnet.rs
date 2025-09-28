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
proof fn lemma_binary_search_correctness(v: Seq<int>, elem: int, p: i32)
    requires 
        sorted(v),
        -1 <= p < v.len(),
        (forall|u: int| 0 <= u <= p ==> v[u] <= elem),
        (forall|w: int| p < w < v.len() ==> v[w] > elem)
    ensures 
        v.contains(elem) <==> (p >= 0 && v[p as int] == elem)
{
    if v.contains(elem) {
        let idx = choose|i: int| 0 <= i < v.len() && v[i] == elem;
        assert(v[idx] == elem);
        
        if idx <= p {
            assert(v[idx] <= elem);
            assert(v[idx] == elem);
        } else {
            assert(p < idx < v.len());
            assert(v[idx] > elem);
            assert(v[idx] == elem);
            assert(false);
        }
        
        assert(idx <= p);
        assert(0 <= idx <= p);
        assert(p >= 0);
        
        if p + 1 < v.len() {
            assert(v[p as int + 1] > elem);
            if v[p as int] > elem {
                assert(idx <= p);
                assert(v[idx] == elem);
                assert(v[p as int] > elem);
                assert(sorted(v));
                assert(forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]);
                assert(idx < p);
                assert(v[idx] <= v[p as int]);
                assert(elem <= v[p as int]);
                assert(v[p as int] > elem);
                assert(false);
            }
        } else {
            assert(v[p as int] <= elem);
            assert(v[p as int] >= elem);
            assert(v[p as int] == elem);
        }
    }
    
    if p >= 0 && v[p as int] == elem {
        assert(v.contains(elem));
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
        lemma_binary_search_correctness(v@, elem, p);
    }
    
    if p >= 0 && v[p as usize] == elem {
        true
    } else {
        false
    }
}
// </vc-code>

fn main() {
    //Recursive binary search
}

}