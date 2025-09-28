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
// Helper lemma to prove properties about the result of binary search
proof fn binary_search_correctness(v: Seq<int>, elem: int, p: int)
    requires
        sorted(v),
        -1 <= p < v.len(),
        forall|u: int| 0 <= u <= p ==> v[u] <= elem,
        forall|w: int| p < w < v.len() ==> v[w] > elem,
    ensures
        v.contains(elem) ==> (0 <= p < v.len() && v[p] == elem),
        (0 <= p < v.len() && v[p] == elem) ==> v.contains(elem),
        !v.contains(elem) ==> (p == -1 || (0 <= p < v.len() && v[p] < elem)),
{
    if v.contains(elem) {
        // There exists some index where v[index] == elem
        let index = choose|i: int| 0 <= i < v.len() && #[trigger] v[i] == elem;
        assert(0 <= index < v.len() && v[index] == elem);
        
        // By the postconditions of binary_search:
        if index <= p {
            // v[index] <= elem, but v[index] == elem, so this is fine
            assert(v[index] <= elem);
        }
        
        if index > p {
            // v[index] > elem, but v[index] == elem, which is a contradiction
            assert(v[index] > elem);
            assert(v[index] == elem);
            assert(false);
        }
        
        // Therefore index <= p
        assert(index <= p);
        
        // Now we need to show that p >= 0
        // Since index >= 0 and index <= p, we have p >= 0
        assert(p >= 0);
        
        // Now we need to show v[p] == elem
        // We know v[p] <= elem (from postcondition)
        // If v[p] < elem, then for all i <= p, v[i] < elem (by sorted property)
        // But v[index] == elem and index <= p, contradiction
        if p > index {
            // By sorted property: v[index] <= v[p]
            // We have v[index] == elem and v[p] <= elem
            // So v[index] <= v[p] <= elem
            // Since v[index] == elem, we get elem <= v[p] <= elem
            // Therefore v[p] == elem
            assert(v[index] <= v[p]);  // by sorted
            assert(v[p] <= elem);       // by postcondition
            assert(elem <= v[p]);       // since v[index] == elem and v[index] <= v[p]
            assert(v[p] == elem);
        } else {
            // p == index
            assert(p == index);
            assert(v[p] == elem);
        }
    }
    
    if 0 <= p < v.len() && v[p] == elem {
        // Trivially v.contains(elem)
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
        binary_search_correctness(v@, elem, p as int);
    }
    
    if p >= 0 && v[p as usize] == elem {
        assert(v@.contains(elem));
        true
    } else {
        assert(!v@.contains(elem));
        false
    }
}
// </vc-code>

fn main() {
    //Recursive binary search
}

}