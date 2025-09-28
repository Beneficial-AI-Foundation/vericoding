use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_no_duplicates(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

proof fn set_difference_properties(a: Seq<int>, b: Seq<int>)
    ensures
        forall|x: int| (a.contains(x) && !b.contains(x)) ==> #[trigger] (a.filter(|e: int| !b.contains(e))).contains(x),
        forall|x: int| #[trigger] (a.filter(|e: int| !b.contains(e))).contains(x) ==> (a.contains(x) && !b.contains(x)),
        contains_no_duplicates(a.filter(|e: int| !b.contains(e)))
{
}

spec fn is_set_difference(diff: Seq<int>, a: Seq<int>, b: Seq<int>) -> bool {
    forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)) &&
    contains_no_duplicates(diff)
}

spec fn index_of(s: Seq<int>, x: int) -> int
    recommends s.contains(x)
{
    choose|idx: int| 0 <= idx < s.len() && s[idx] == x
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j),
// </vc-spec>
// <vc-code>
{
    let mut diff = Vec::new();
    let mut seen = Vec::new();
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: int| diff@.contains(x) ==> (a.contains(x) && !b.contains(x)),
            forall|x: int| (a.contains(x) && !b.contains(x) && (exists|idx: int| 0 <= idx < a.len() && idx < i && a@[idx] == x)) ==> diff@.contains(x),
            forall|k: int, l: int| 0 <= k < l < diff@.len() ==> diff@[k] != diff@[l],
            seen@.len() == diff@.len(),
            forall|j: int| 0 <= j < diff@.len() ==> diff@[j] == seen@[j],
    {
        let elem = a[i];
        if !b.contains(elem) {
            if !seen.contains(elem) {
                diff.push(elem);
                seen.push(elem);
            }
        }
        i += 1;
    }
    
    proof {
        assert forall|x: int| diff@.contains(x) implies (a.contains(x) && !b.contains(x)) by {
            assert(diff@.contains(x) ==> (a.contains(x) && !b.contains(x)));
        }
        
        assert forall|x: int| (a.contains(x) && !b.contains(x)) implies diff@.contains(x) by {
            if a.contains(x) && !b.contains(x) {
                let idx = index_of(a, x);
                assert(0 <= idx < a.len() as int);
                assert(idx < i as int);
            }
        }
        
        assert forall|i: int, j: int| 0 <= i < j < diff@.len() implies diff@[i] != diff@[j] by {
            assert(diff@[i] != diff@[j]);
        }
    }
    
    diff.into()
}
// </vc-code>

fn main() {}

}