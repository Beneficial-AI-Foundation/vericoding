use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Seq<int>) -> bool {
    forall |j: int, k: int| 0 <= j < k < a.len() ==> a.spec_index(j) <= a.spec_index(k)
}

spec fn unique_spec(a: Seq<int>) -> bool {
    forall |j: int, k: int| 0 <= j < k < a.len() ==> a.spec_index(j) != a.spec_index(k)
}

spec fn subsequence_of(b: Seq<int>, a: Seq<int>) -> bool {
    forall |i: int| 0 <= i < b.len() ==> exists |j: int| 0 <= j < a.len() && b.spec_index(i) == a.spec_index(j)
}

fn unique(a: Seq<int>) -> (b: Seq<int>)
    requires
        sorted(a)
    ensures
        sorted(b),
        unique_spec(b),
        subsequence_of(b, a)
{
    if a.len() == 0 {
        return Seq::empty();
    }
    
    let mut result: Vec<int> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sorted(a),
            sorted(result@),
            unique_spec(result@),
            subsequence_of(result@, a),
            i > 0 ==> result.len() > 0,
            result.len() > 0 ==> result@.spec_index(result.len() as int - 1) == a.spec_index(i as int - 1) || 
                                 exists |k: int| 0 <= k < i && result@.spec_index(result.len() as int - 1) == a.spec_index(k)
    {
        let current = a.spec_index(i as int);
        if result.len() == 0 || current != result@.spec_index(result.len() as int - 1) {
            result.push(current);
            
            // Proof that sorted property is maintained
            assert forall |j: int, k: int| 0 <= j < k < result@.len() implies result@.spec_index(j) <= result@.spec_index(k) by {
                if k == result@.len() - 1 {
                    if j == result@.len() - 2 {
                        // Just added element, prove it's >= previous
                        if result.len() > 1 {
                            assert(current >= result@.spec_index(result.len() as int - 2));
                        }
                    } else {
                        // Inductive case
                        assert(result@.spec_index(j) <= result@.spec_index(k));
                    }
                } else {
                    // Elements before the newly added one
                    assert(result@.spec_index(j) <= result@.spec_index(k));
                }
            };
            
            // Proof that unique property is maintained
            assert forall |j: int, k: int| 0 <= j < k < result@.len() implies result@.spec_index(j) != result@.spec_index(k) by {
                if k == result@.len() - 1 {
                    // Just added element is different from all previous
                    assert(result@.spec_index(j) != current);
                } else {
                    // Inductive case
                    assert(result@.spec_index(j) != result@.spec_index(k));
                }
            };
        }
        i = i + 1;
    }
    
    result@
}

}