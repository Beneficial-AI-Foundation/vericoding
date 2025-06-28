use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to establish set properties
proof fn lemma_set_insert_size<T>(s: Set<T>, x: T)
    requires !s.contains(x)
    ensures s.insert(x).len() == s.len() + 1
{
    // This is a built-in property of sets in Verus
    // The proof is automatic when the precondition is met
}

proof fn lemma_set_equal_size<T>(s1: Set<T>, s2: Set<T>)
    requires s1 =~= s2
    ensures s1.len() == s2.len()
{
    // Set equality implies equal cardinality - this is automatic in Verus
}

fn CountIdenticalPositions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: int)
    requires
        a.len() == b.len() && b.len() == c.len()
    ensures
        count >= 0,
        count == (set|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len()
{
    let mut count = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count >= 0,
            count == (set|j: int| 0 <= j < i && a[j] == b[j] && b[j] == c[j]).len(),
            a.len() == b.len() && b.len() == c.len()
        decreases a.len() - i
    {
        if a[i] == b[i] && b[i] == c[i] {
            // Prove that adding element i increases the set size by 1
            let old_set = set|j: int| 0 <= j < i && a[j] == b[j] && b[j] == c[j];
            let new_set = set|j: int| 0 <= j < i + 1 && a[j] == b[j] && b[j] == c[j];
            
            // Prove i is not in old_set
            assert(!old_set.contains(i)) by {
                if old_set.contains(i) {
                    assert(0 <= i < i); // contradiction since i < i is false
                    assert(false);
                }
            }
            
            // Prove i is in new_set
            assert(new_set.contains(i)) by {
                assert(0 <= i < i + 1);
                assert(a[i] == b[i] && b[i] == c[i]);
            }
            
            // Prove new_set is exactly old_set.insert(i)
            assert(new_set =~= old_set.insert(i)) by {
                assert(forall|j: int| new_set.contains(j) <==> (old_set.contains(j) || j == i)) by {
                    if new_set.contains(j) {
                        assert(0 <= j < i + 1);
                        assert(a[j] == b[j] && b[j] == c[j]);
                        if j < i {
                            assert(0 <= j < i);
                            assert(old_set.contains(j));
                        } else {
                            assert(j == i);
                        }
                    }
                    if old_set.contains(j) {
                        assert(0 <= j < i);
                        assert(a[j] == b[j] && b[j] == c[j]);
                        assert(0 <= j < i + 1);
                        assert(new_set.contains(j));
                    }
                    if j == i {
                        assert(new_set.contains(j));
                    }
                }
            }
            
            lemma_set_insert_size(old_set, i);
            assert(new_set.len() == old_set.len() + 1);
            
            count = count + 1;
        } else {
            // Prove that not adding element i keeps the set size the same
            let old_set = set|j: int| 0 <= j < i && a[j] == b[j] && b[j] == c[j];
            let new_set = set|j: int| 0 <= j < i + 1 && a[j] == b[j] && b[j] == c[j];
            
            // i doesn't satisfy the condition, so it's not in new_set
            assert(!new_set.contains(i)) by {
                if new_set.contains(i) {
                    assert(0 <= i < i + 1);
                    assert(a[i] == b[i] && b[i] == c[i]); 
                    assert(false); // contradiction with the else condition
                }
            }
            
            // Prove new_set == old_set
            assert(new_set =~= old_set) by {
                assert(forall|j: int| new_set.contains(j) <==> old_set.contains(j)) by {
                    if new_set.contains(j) {
                        assert(0 <= j < i + 1);
                        assert(a[j] == b[j] && b[j] == c[j]);
                        if j == i {
                            assert(false); // we proved i is not in new_set
                        } else {
                            assert(j < i);
                            assert(0 <= j < i);
                            assert(old_set.contains(j));
                        }
                    }
                    if old_set.contains(j) {
                        assert(0 <= j < i);
                        assert(a[j] == b[j] && b[j] == c[j]);
                        assert(0 <= j < i + 1);
                        assert(new_set.contains(j));
                    }
                }
            }
            
            lemma_set_equal_size(new_set, old_set);
            assert(new_set.len() == old_set.len());
        }
        i = i + 1;
    }
    
    count
}

}