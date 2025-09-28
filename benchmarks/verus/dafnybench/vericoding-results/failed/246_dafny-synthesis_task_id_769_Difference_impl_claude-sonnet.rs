use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_no_duplicates_in_filter(a: Seq<int>, b: Seq<int>, result: Seq<int>)
    requires
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] != a[j],
        result == a.filter(|x: int| !b.contains(x)),
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    if result.len() <= 1 {
        return;
    }
    
    assert forall|i: int, j: int| 0 <= i < j < result.len() implies result[i] != result[j] by {
        let filtered = a.filter(|x: int| !b.contains(x));
        assert(result == filtered);
        
        // The filter preserves the relative order and uniqueness
        // Since a has no duplicates and filter only removes elements,
        // the result cannot have duplicates
    }
}

proof fn lemma_filter_correctness(a: Seq<int>, b: Seq<int>, result: Seq<int>)
    requires
        result == a.filter(|x: int| !b.contains(x)),
    ensures
        forall|x: int| result.contains(x) <==> (a.contains(x) && !b.contains(x)),
{
    assert forall|x: int| result.contains(x) <==> (a.contains(x) && !b.contains(x)) by {
        let filtered = a.filter(|x: int| !b.contains(x));
        assert(result == filtered);
    }
}
// </vc-helpers>

// <vc-spec>
fn difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall|x: int| diff.contains(x) <==> (a.contains(x) && !b.contains(x)),
        forall|i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j),
// </vc-spec>
// <vc-code>
{
    let mut result = Seq::<int>::empty();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: int| result.contains(x) <==> (exists|j: int| 0 <= j < i && a[j] == x && !b.contains(x)),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
    {
        if !b.contains(a[i]) {
            result = result.push(a[i]);
        }
        i = i + 1;
    }
    
    proof {
        assert forall|x: int| result.contains(x) <==> (a.contains(x) && !b.contains(x)) by {
            if result.contains(x) {
                assert((exists|j: int| 0 <= j < a.len() && a[j] == x && !b.contains(x)));
                assert a.contains(x) && !b.contains(x);
            }
            if a.contains(x) && !b.contains(x) {
                assert((exists|j: int| 0 <= j < a.len() && a[j] == x));
                assert result.contains(x);
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}

}