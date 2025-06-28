use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountIdenticalPositions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: int)
    requires
        a.len() == b.len() && b.len() == c.len()
    ensures
        count >= 0,
        count == (set|i: int| 0 <= i < a.len() && a.spec_index(i) == b.spec_index(i) && b.spec_index(i) == c.spec_index(i)).len()
{
    let mut count = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count >= 0,
            count == (set|j: int| 0 <= j < i && a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j)).len(),
            a.len() == b.len() && b.len() == c.len()
    {
        if a.spec_index(i) == b.spec_index(i) && b.spec_index(i) == c.spec_index(i) {
            // Prove that adding element i increases the set size by 1
            let old_set = set|j: int| 0 <= j < i && a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j);
            let new_set = set|j: int| 0 <= j < i + 1 && a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j);
            
            // Key insight: new_set contains all elements of old_set plus potentially i
            assert forall|j: int| old_set.contains(j) implies new_set.contains(j) by {
                if old_set.contains(j) {
                    assert(0 <= j < i);
                    assert(a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j));
                    assert(0 <= j < i + 1);
                }
            };
            
            // i satisfies the condition and is in new_set but not old_set
            assert(new_set.contains(i));
            assert(!old_set.contains(i)) by {
                if old_set.contains(i) {
                    assert(0 <= i < i); // contradiction
                    assert(false);
                }
            };
            
            // new_set is exactly old_set union {i}
            assert forall|j: int| new_set.contains(j) implies (old_set.contains(j) || j == i) by {
                if new_set.contains(j) {
                    assert(0 <= j < i + 1);
                    assert(a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j));
                    if j < i {
                        assert(old_set.contains(j));
                    } else {
                        assert(j == i);
                    }
                }
            };
            
            assert(new_set =~= old_set.insert(i));
            assert(new_set.len() == old_set.len() + 1);
            
            count = count + 1;
        } else {
            // Prove that not adding element i keeps the set size the same
            let old_set = set|j: int| 0 <= j < i && a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j);
            let new_set = set|j: int| 0 <= j < i + 1 && a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j);
            
            // i doesn't satisfy the condition, so new_set == old_set
            assert(!new_set.contains(i)) by {
                if new_set.contains(i) {
                    assert(a.spec_index(i) == b.spec_index(i) && b.spec_index(i) == c.spec_index(i)); // contradiction
                    assert(false);
                }
            };
            
            assert forall|j: int| old_set.contains(j) iff new_set.contains(j) by {
                if old_set.contains(j) {
                    assert(0 <= j < i);
                    assert(0 <= j < i + 1);
                    assert(new_set.contains(j));
                }
                if new_set.contains(j) {
                    assert(0 <= j < i + 1);
                    if j == i {
                        assert(false); // we proved i is not in new_set
                    } else {
                        assert(j < i);
                        assert(old_set.contains(j));
                    }
                }
            };
            
            assert(new_set =~= old_set);
            assert(new_set.len() == old_set.len());
        }
        i = i + 1;
    }
    
    count
}

}