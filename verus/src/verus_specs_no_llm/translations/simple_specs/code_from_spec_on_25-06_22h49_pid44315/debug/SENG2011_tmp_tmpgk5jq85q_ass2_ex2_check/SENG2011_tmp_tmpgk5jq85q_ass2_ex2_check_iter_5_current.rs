use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sorted(a: Seq<char>, low: int, high: int) -> bool
recommends 0 <= low <= high <= a.len()
{ 
    forall|j: int, k: int| low <= j < k < high ==> a[j] <= a[k]
}

fn String3Sort(a: Seq<char>) -> (b: Seq<char>)
    requires a.len() == 3
    ensures Sorted(b, 0, b.len() as int)
    ensures a.len() == b.len()
    ensures multiset![b[0], b[1], b[2]] == multiset![a[0], a[1], a[2]]
{
    let c0 = a[0];
    let c1 = a[1]; 
    let c2 = a[2];
    
    let result = if c0 <= c1 && c1 <= c2 {
        // Already sorted: c0 <= c1 <= c2
        seq![c0, c1, c2]
    } else if c0 <= c2 && c2 <= c1 {
        // c0 <= c2 <= c1
        seq![c0, c2, c1]
    } else if c1 <= c0 && c0 <= c2 {
        // c1 <= c0 <= c2
        seq![c1, c0, c2]
    } else if c1 <= c2 && c2 <= c0 {
        // c1 <= c2 <= c0
        seq![c1, c2, c0]
    } else if c2 <= c0 && c0 <= c1 {
        // c2 <= c0 <= c1
        seq![c2, c0, c1]
    } else {
        // c2 <= c1 <= c0
        seq![c2, c1, c0]
    };
    
    // Proof that the result has the correct length
    assert(result.len() == 3);
    assert(result.len() == a.len());
    
    // Proof that multiset property holds
    assert(multiset![result[0], result[1], result[2]] == multiset![c0, c1, c2]);
    assert(multiset![c0, c1, c2] == multiset![a[0], a[1], a[2]]);
    
    // Prove that each branch produces a sorted sequence
    if c0 <= c1 && c1 <= c2 {
        assert(result == seq![c0, c1, c2]);
        assert(result[0] <= result[1] <= result[2]);
    } else if c0 <= c2 && c2 <= c1 {
        assert(result == seq![c0, c2, c1]);
        assert(result[0] <= result[1] <= result[2]);
    } else if c1 <= c0 && c0 <= c2 {
        assert(result == seq![c1, c0, c2]);
        assert(result[0] <= result[1] <= result[2]);
    } else if c1 <= c2 && c2 <= c0 {
        assert(result == seq![c1, c2, c0]);
        assert(result[0] <= result[1] <= result[2]);
    } else if c2 <= c0 && c0 <= c1 {
        assert(result == seq![c2, c0, c1]);
        assert(result[0] <= result[1] <= result[2]);
    } else {
        // Prove by exhaustion that we must have c2 <= c1 <= c0
        assert(result == seq![c2, c1, c0]);
        
        // Prove that this case must hold by elimination
        assert(!(c0 <= c1 && c1 <= c2));
        assert(!(c0 <= c2 && c2 <= c1));
        assert(!(c1 <= c0 && c0 <= c2));
        assert(!(c1 <= c2 && c2 <= c0));
        assert(!(c2 <= c0 && c0 <= c1));
        
        // Use the fact that for any two elements x, y, either x <= y or y <= x
        assert(c0 <= c1 || c1 <= c0);
        assert(c0 <= c2 || c2 <= c0);
        assert(c1 <= c2 || c2 <= c1);
        
        // Since we've eliminated all other cases, we must have c2 <= c1 <= c0
        assert(c2 <= c1) by {
            if c1 <= c2 {
                // If c1 <= c2, then combined with c0 <= c1 || c1 <= c0 and c0 <= c2 || c2 <= c0
                // we would have hit one of the previous cases
                assert(c1 <= c0 || c0 <= c1);
                assert(c2 <= c0 || c0 <= c2);
                if c0 <= c1 && c1 <= c2 {
                    assert(false); // contradiction with first case
                } else if c1 <= c0 && c0 <= c2 {
                    assert(false); // contradiction with third case
                } else if c1 <= c2 && c2 <= c0 {
                    assert(false); // contradiction with fourth case
                }
            }
        }
        
        assert(c1 <= c0) by {
            if c0 <= c1 {
                assert(c2 <= c1); // proven above
                if c0 <= c2 {
                    assert(false); // would be case 2: c0 <= c2 <= c1 (since c2 <= c1)
                } else {
                    assert(c2 <= c0); // by trichotomy
                    assert(false); // would be case 5: c2 <= c0 <= c1
                }
            }
        }
        
        assert(c2 <= c1 && c1 <= c0);
        assert(result[0] <= result[1] <= result[2]);
    }
    
    // Now prove the Sorted predicate
    assert forall|j: int, k: int| 0 <= j < k < 3 implies result[j] <= result[k] by {
        // We've proven that result[0] <= result[1] <= result[2] in all cases
        if j == 0 && k == 1 {
            assert(result[0] <= result[1]);
        } else if j == 0 && k == 2 {
            assert(result[0] <= result[1] && result[1] <= result[2]);
        } else if j == 1 && k == 2 {
            assert(result[1] <= result[2]);
        }
    };
    
    result
}

fn check() -> (result: bool)
{
    let test_seq = seq!['c', 'a', 'b'];
    let sorted_seq = String3Sort(test_seq);
    
    // Check if the result is sorted
    sorted_seq[0] <= sorted_seq[1] && sorted_seq[1] <= sorted_seq[2]
}

}