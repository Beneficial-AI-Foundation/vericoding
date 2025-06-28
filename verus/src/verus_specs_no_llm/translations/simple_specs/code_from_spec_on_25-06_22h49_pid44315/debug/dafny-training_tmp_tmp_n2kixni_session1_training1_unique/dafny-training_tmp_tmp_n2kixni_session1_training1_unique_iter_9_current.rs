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
                i > 0 && result@.spec_index(result@.len() - 1) <= a.spec_index((i - 1) as int)
            )
    {
        let current = a.spec_index(i as int);
        
        if result.len() == 0 {
            result.push(current);
            
            // Prove invariants after first push
            assert(result@.len() == 1);
            assert(result@.spec_index(0) == current);
            assert(sorted(result@));
            assert(unique_spec(result@));
            assert(subsequence_of(result@, a)) by {
                assert(exists |j: int| 0 <= j < a.len() && current == a.spec_index(j)) by {
                    assert(0 <= i as int < a.len());
                    assert(current == a.spec_index(i as int));
                };
            };
        } else {
            let last_val = result@.spec_index(result@.len() - 1);
            if current != last_val {
                let old_result = result@;
                result.push(current);
                
                // Prove sortedness is maintained
                assert(sorted(result@)) by {
                    assert(sorted(old_result));
                    assert(result@ == old_result.push(current));
                    assert(last_val <= current) by {
                        assert(i > 0);
                        assert(last_val <= a.spec_index((i - 1) as int));
                        assert(a.spec_index((i - 1) as int) <= current) by {
                            assert(sorted(a));
                            assert(0 <= (i - 1) as int < i as int < a.len());
                        };
                    };
                };
                
                // Prove uniqueness is maintained
                assert(unique_spec(result@)) by {
                    assert(unique_spec(old_result));
                    assert(result@ == old_result.push(current));
                    assert(current != last_val);
                    assert(forall |j: int| 0 <= j < old_result.len() ==> old_result.spec_index(j) != current) by {
                        if exists |j: int| 0 <= j < old_result.len() && old_result.spec_index(j) == current {
                            let j = choose |j: int| 0 <= j < old_result.len() && old_result.spec_index(j) == current;
                            assert(sorted(old_result));
                            assert(j < old_result.len() - 1 ==> old_result.spec_index(j) <= last_val);
                            assert(j == old_result.len() - 1 ==> old_result.spec_index(j) == last_val);
                            assert(false);
                        }
                    };
                };
                
                // Prove subsequence property is maintained
                assert(subsequence_of(result@, a)) by {
                    assert(subsequence_of(old_result, a));
                    assert(result@ == old_result.push(current));
                    assert(exists |j: int| 0 <= j < a.len() && current == a.spec_index(j)) by {
                        assert(0 <= i as int < a.len());
                        assert(current == a.spec_index(i as int));
                    };
                };
            }
        }
        
        i = i + 1;
    }
    
    result@
}

}