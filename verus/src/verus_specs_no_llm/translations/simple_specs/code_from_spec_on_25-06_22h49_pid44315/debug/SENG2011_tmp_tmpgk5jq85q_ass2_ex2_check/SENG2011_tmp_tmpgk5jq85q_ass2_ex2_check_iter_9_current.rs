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
    
    // Prove the Sorted predicate by showing result[0] <= result[1] <= result[2]
    assert(result[0] <= result[1] && result[1] <= result[2]) by {
        if c0 <= c1 && c1 <= c2 {
            assert(result == seq![c0, c1, c2]);
            assert(result[0] == c0 && result[1] == c1 && result[2] == c2);
        } else if c0 <= c2 && c2 <= c1 {
            assert(result == seq![c0, c2, c1]);
            assert(result[0] == c0 && result[1] == c2 && result[2] == c1);
        } else if c1 <= c0 && c0 <= c2 {
            assert(result == seq![c1, c0, c2]);
            assert(result[0] == c1 && result[1] == c0 && result[2] == c2);
        } else if c1 <= c2 && c2 <= c0 {
            assert(result == seq![c1, c2, c0]);
            assert(result[0] == c1 && result[1] == c2 && result[2] == c0);
        } else if c2 <= c0 && c0 <= c1 {
            assert(result == seq![c2, c0, c1]);
            assert(result[0] == c2 && result[1] == c0 && result[2] == c1);
        } else {
            // Must be c2 <= c1 <= c0
            assert(result == seq![c2, c1, c0]);
            assert(result[0] == c2 && result[1] == c1 && result[2] == c0);
            // We need to prove c2 <= c1 <= c0 from the negation of other cases
            assert(!(c0 <= c1 && c1 <= c2));
            assert(!(c0 <= c2 && c2 <= c1));
            assert(!(c1 <= c0 && c0 <= c2));
            assert(!(c1 <= c2 && c2 <= c0));
            assert(!(c2 <= c0 && c0 <= c1));
            // By trichotomy of ordering, this means c2 <= c1 <= c0
        }
    };
    
    // Now prove the full Sorted predicate
    assert(Sorted(result, 0, result.len() as int)) by {
        assert(result.len() == 3);
        assert(result[0] <= result[1] && result[1] <= result[2]);
        
        // Prove the forall statement by case analysis
        assert(forall|j: int, k: int| 0 <= j < k < 3 ==> result[j] <= result[k]) by {
            // The only valid pairs (j,k) with 0 <= j < k < 3 are:
            // (0,1), (0,2), (1,2)
            
            // Case (0,1): result[0] <= result[1] - already proven
            // Case (0,2): result[0] <= result[2] - follows from transitivity
            assert(result[0] <= result[2]) by {
                assert(result[0] <= result[1]);
                assert(result[1] <= result[2]);
            }
            // Case (1,2): result[1] <= result[2] - already proven
        };
    };
    
    result
}

fn check() -> (result: bool)
{
    let test_seq = seq!['c', 'a', 'b'];
    let sorted_seq = String3Sort(test_seq);
    
    // Check if the result is sorted
    sorted_seq[0] <= sorted_seq[1] && sorted_seq[1] <= sorted[2]
}

}