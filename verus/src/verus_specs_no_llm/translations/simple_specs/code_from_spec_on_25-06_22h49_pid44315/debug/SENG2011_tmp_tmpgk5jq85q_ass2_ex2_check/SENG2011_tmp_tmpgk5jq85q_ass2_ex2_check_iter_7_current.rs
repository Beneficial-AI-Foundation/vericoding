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
    
    // Prove that the result is sorted by examining all cases
    if c0 <= c1 && c1 <= c2 {
        assert(result[0] == c0 && result[1] == c1 && result[2] == c2);
        assert(result[0] <= result[1] <= result[2]);
    } else if c0 <= c2 && c2 <= c1 {
        assert(result[0] == c0 && result[1] == c2 && result[2] == c1);
        assert(result[0] <= result[1] <= result[2]);
    } else if c1 <= c0 && c0 <= c2 {
        assert(result[0] == c1 && result[1] == c0 && result[2] == c2);
        assert(result[0] <= result[1] <= result[2]);
    } else if c1 <= c2 && c2 <= c0 {
        assert(result[0] == c1 && result[1] == c2 && result[2] == c0);
        assert(result[0] <= result[1] <= result[2]);
    } else if c2 <= c0 && c0 <= c1 {
        assert(result[0] == c2 && result[1] == c0 && result[2] == c1);
        assert(result[0] <= result[1] <= result[2]);
    } else {
        assert(result[0] == c2 && result[1] == c1 && result[2] == c0);
        // Prove that this case must be c2 <= c1 <= c0
        assert(!(c0 <= c1 && c1 <= c2));
        assert(!(c0 <= c2 && c2 <= c1));
        assert(!(c1 <= c0 && c0 <= c2));
        assert(!(c1 <= c2 && c2 <= c0));
        assert(!(c2 <= c0 && c0 <= c1));
        
        // By total ordering of chars, we can deduce c2 <= c1 <= c0
        // Since we don't have c2 <= c0, we have c0 < c2
        // Since we don't have c1 <= c0, we have c0 < c1
        // Since we don't have c0 <= c1, we have c1 < c0 (contradiction with above)
        // The only consistent ordering is c2 <= c1 <= c0
        assert(c2 <= c1 <= c0);
        assert(result[0] <= result[1] <= result[2]);
    }
    
    // Prove the Sorted predicate
    assert(forall|j: int, k: int| 0 <= j < k < 3 ==> result[j] <= result[k]) by {
        // Since we have a sequence of length 3, we only need to check:
        // j=0, k=1: result[0] <= result[1]
        // j=0, k=2: result[0] <= result[2]  
        // j=1, k=2: result[1] <= result[2]
        
        // We've proven result[0] <= result[1] <= result[2] above
        // This implies all three conditions
        assert(result[0] <= result[1]);
        assert(result[1] <= result[2]);
        assert(result[0] <= result[2]); // by transitivity
        
        // The forall condition holds for all valid j, k
        assert(forall|j: int, k: int| 0 <= j < k < 3 ==> #[trigger] (j == 0 && k == 1) || (j == 0 && k == 2) || (j == 1 && k == 2));
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