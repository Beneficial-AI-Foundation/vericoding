use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn RotateRight(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires
        n >= 0
    ensures
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.spec_index(i) == l.spec_index((i - n + l.len()) % l.len())
{
    if l.len() == 0 {
        return l;
    }
    
    let effective_n = n % (l.len() as int);
    let split_point = (l.len() - effective_n) % (l.len() as int);
    
    let left_part = l.subrange(0, split_point);
    let right_part = l.subrange(split_point, l.len() as int);
    
    let result = right_part + left_part;
    
    // Basic length properties
    assert(result.len() == right_part.len() + left_part.len());
    assert(right_part.len() == l.len() - split_point);
    assert(left_part.len() == split_point);
    assert(result.len() == l.len());
    
    // Key lemma: split_point + effective_n = l.len()
    assert(split_point + effective_n == l.len()) by {
        assert(split_point == (l.len() - effective_n) % l.len());
        assert(effective_n == n % l.len());
        assert(0 <= effective_n < l.len());
        assert(l.len() - effective_n >= 0);
        assert(l.len() - effective_n < l.len());
        assert(split_point == l.len() - effective_n);
    };
    
    // Prove the main postcondition
    assert forall|i: int| 0 <= i < result.len() implies {
        let original_index = (i - n + l.len()) % l.len();
        result.spec_index(i) == l.spec_index(original_index)
    } by {
        if 0 <= i < result.len() {
            let original_index = (i - n + l.len()) % l.len();
            
            if i < right_part.len() {
                // i is in the right part of result
                assert(result.spec_index(i) == right_part.spec_index(i));
                assert(right_part.spec_index(i) == l.spec_index(split_point + i));
                
                // Show that (split_point + i) == original_index
                assert(split_point + i == original_index) by {
                    // We know split_point + effective_n == l.len()
                    // And effective_n == n % l.len()
                    // So split_point == l.len() - (n % l.len())
                    
                    // original_index = (i - n + l.len()) % l.len()
                    // We want to show split_point + i = (i - n + l.len()) % l.len()
                    
                    let target = i - n + l.len();
                    assert(split_point + i == l.len() - effective_n + i);
                    assert(effective_n == n % l.len());
                    
                    // Case analysis on whether n >= l.len()
                    if n < l.len() {
                        assert(effective_n == n);
                        assert(split_point + i == l.len() - n + i);
                        assert(target == i - n + l.len());
                        assert(split_point + i == target);
                        assert(0 <= split_point + i < l.len());
                        assert(original_index == split_point + i);
                    } else {
                        // General case: use modular arithmetic properties
                        assert((target) % l.len() == (l.len() - effective_n + i) % l.len());
                        assert(split_point == l.len() - effective_n);
                        assert(0 <= split_point + i < l.len());
                        assert((split_point + i) % l.len() == split_point + i);
                        assert(original_index == split_point + i);
                    }
                };
                
            } else {
                // i is in the left part of result
                let left_index = i - right_part.len();
                assert(result.spec_index(i) == left_part.spec_index(left_index));
                assert(left_part.spec_index(left_index) == l.spec_index(left_index));
                
                // Show that left_index == original_index
                assert(left_index == original_index) by {
                    assert(left_index == i - right_part.len());
                    assert(right_part.len() == l.len() - split_point);
                    assert(left_index == i - (l.len() - split_point));
                    assert(left_index == i - l.len() + split_point);
                    
                    // We know split_point + effective_n == l.len()
                    assert(split_point == l.len() - effective_n);
                    assert(left_index == i - l.len() + l.len() - effective_n);
                    assert(left_index == i - effective_n);
                    
                    let target = i - n + l.len();
                    assert(effective_n == n % l.len());
                    
                    // Show (i - n + l.len()) % l.len() == i - effective_n
                    assert((target) % l.len() == (i - effective_n) % l.len()) by {
                        assert(target == i - n + l.len());
                        assert(n == effective_n + (n / l.len()) * l.len());
                        assert(target == i - (effective_n + (n / l.len()) * l.len()) + l.len());
                        assert(target == i - effective_n + l.len() - (n / l.len()) * l.len());
                        assert(target == i - effective_n + l.len() * (1 - n / l.len()));
                    };
                    
                    assert(0 <= left_index < l.len());
                    assert((i - effective_n) % l.len() == i - effective_n);
                    assert(original_index == left_index);
                };
            }
        }
    };
    
    result
}

}