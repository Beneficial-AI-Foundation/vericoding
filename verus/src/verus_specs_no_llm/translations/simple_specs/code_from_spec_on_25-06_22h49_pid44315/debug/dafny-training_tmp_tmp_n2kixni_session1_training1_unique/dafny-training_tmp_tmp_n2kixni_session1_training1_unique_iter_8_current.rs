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
            result@.len() > 0 ==> (
                i > 0 && result@.last() <= a.spec_index((i - 1) as int)
            )
    {
        let current = a.spec_index(i as int);
        
        if result.len() == 0 {
            result.push(current);
        } else {
            let last_val = result@.last();
            if current != last_val {
                // Prove that adding current maintains sortedness
                assert(sorted(a));
                if i > 0 {
                    assert(last_val <= a.spec_index((i - 1) as int));
                    assert(a.spec_index((i - 1) as int) <= current) by {
                        assert((i - 1) as int < i as int);
                        assert(0 <= (i - 1) as int < i as int < a.len());
                        assert(sorted(a));
                    };
                    assert(last_val <= current);
                }
                
                result.push(current);
            }
        }
        
        i = i + 1;
    }
    
    result@
}

}