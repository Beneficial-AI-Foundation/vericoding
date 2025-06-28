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
            // Additional invariants to help verification
            forall |idx: int| 0 <= idx < result@.len() ==> 
                exists |j: int| 0 <= j < i && result@.spec_index(idx) == a.spec_index(j),
            result.len() > 0 ==> result@.spec_index(result.len() as int - 1) <= 
                (if i > 0 { a.spec_index(i as int - 1) } else { result@.spec_index(result.len() as int - 1) })
    {
        let current = a.spec_index(i as int);
        
        if result.len() == 0 || current != result@.spec_index(result.len() as int - 1) {
            // Prove that adding current maintains sorted property
            proof {
                if result.len() > 0 {
                    let last_idx = result.len() as int - 1;
                    let last_val = result@.spec_index(last_idx);
                    
                    // Since a is sorted and we're going through it sequentially,
                    // current >= last element in result
                    if i > 0 {
                        // Find where last_val appears in a
                        assert(exists |k: int| 0 <= k < i && last_val == a.spec_index(k));
                        // Since a is sorted and k < i, last_val <= current
                        assert(last_val <= current);
                    }
                }
            }
            
            result.push(current);
            
            // Prove properties are maintained after push
            proof {
                let new_len = result@.len();
                
                // Prove sorted property
                assert forall |j: int, k: int| 0 <= j < k < new_len 
                ==> result@.spec_index(j) <= result@.spec_index(k) by {
                    if k == new_len - 1 {
                        // k points to the newly added element
                        if j < new_len - 1 {
                            // j points to an old element
                            // We proved above that old elements <= current
                            assert(result@.spec_index(j) <= current);
                        }
                    } else {
                        // Both j and k point to old elements, sorted by induction
                    }
                };
                
                // Prove unique property
                assert forall |j: int, k: int| 0 <= j < k < new_len 
                ==> result@.spec_index(j) != result@.spec_index(k) by {
                    if k == new_len - 1 {
                        // k points to newly added element
                        if j < new_len - 1 {
                            // j points to old element
                            if j == new_len - 2 {
                                // j is the previous last element
                                // We only added current if it's different
                                assert(result@.spec_index(j) != current);
                            } else {
                                // Since result was sorted and unique before,
                                // and current > last element, current != any old element
                                assert(result@.spec_index(j) != current);
                            }
                        }
                    } else {
                        // Both point to old elements, unique by induction
                    }
                };
                
                // Prove subsequence property
                assert forall |idx: int| 0 <= idx < new_len 
                ==> exists |j: int| 0 <= j < a.len() && result@.spec_index(idx) == a.spec_index(j) by {
                    if idx == new_len - 1 {
                        // Newly added element comes from a[i]
                        assert(result@.spec_index(idx) == a.spec_index(i as int));
                    } else {
                        // Old elements satisfied this by induction
                    }
                };
            }
        }
        i = i + 1;
    }
    
    result@
}

}