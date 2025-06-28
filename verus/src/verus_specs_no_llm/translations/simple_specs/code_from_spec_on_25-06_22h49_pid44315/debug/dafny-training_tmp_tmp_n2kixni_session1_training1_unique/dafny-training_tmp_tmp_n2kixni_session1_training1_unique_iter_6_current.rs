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
            forall |idx: int| 0 <= idx < result@.len() ==> 
                exists |j: int| 0 <= j < i && result@.spec_index(idx) == a.spec_index(j),
            i > 0 && result@.len() > 0 ==> result@.last() <= a.spec_index((i - 1) as int),
            forall |j: int, k: int| 0 <= j < k < i ==> a.spec_index(j) <= a.spec_index(k)
    {
        let current = a.spec_index(i as int);
        
        if result.len() == 0 {
            result.push(current);
            
            // Prove invariants for first element
            assert(sorted(result@));
            assert(unique_spec(result@));
            assert(subsequence_of(result@, a)) by {
                assert(result@.spec_index(0) == current);
                assert(current == a.spec_index(i as int));
            }
        } else if current != result@.last() {
            // Proof that current maintains sortedness
            assert(sorted(a)) by {
                // a is sorted from precondition
            }
            assert(i > 0);
            assert(result@.last() <= a.spec_index((i - 1) as int)) by {
                // from loop invariant
            }
            assert(a.spec_index((i - 1) as int) <= current) by {
                assert(sorted(a));
                assert(0 <= (i - 1) as int < i as int < a.len());
            }
            assert(result@.last() <= current);
            
            let old_result = result@;
            result.push(current);
            
            // Prove sorted property is maintained
            assert(sorted(result@)) by {
                assert(sorted(old_result));
                assert(old_result.len() > 0);
                assert(old_result.last() <= current);
                assert(result@ == old_result.push(current));
            }
            
            // Prove unique property is maintained
            assert(unique_spec(result@)) by {
                assert(unique_spec(old_result));
                assert(current != old_result.last());
                assert(result@ == old_result.push(current));
            }
            
            // Prove subsequence property is maintained
            assert(subsequence_of(result@, a)) by {
                assert(subsequence_of(old_result, a));
                assert(current == a.spec_index(i as int));
                assert(result@ == old_result.push(current));
            }
        }
        
        i = i + 1;
    }
    
    result@
}

}