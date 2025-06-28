use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsSublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i <= main.len() - sub.len() && sub == main.subrange(i, i + sub.len()))
{
    if sub.len() > main.len() {
        // When sub is longer than main, no valid positions exist
        assert(forall|i: int| 0 <= i <= main.len() - sub.len() ==> false) by {
            // Since sub.len() > main.len(), we have main.len() - sub.len() < 0
            // So there's no i such that 0 <= i <= main.len() - sub.len()
        };
        return false;
    }
    
    if sub.len() == 0 {
        // Empty subsequence exists at position 0
        assert(sub == main.subrange(0, 0)) by {
            assert(sub == Seq::<int>::empty());
            assert(main.subrange(0, 0) == Seq::<int>::empty());
        };
        return true;
    }
    
    // At this point: 0 < sub.len() <= main.len()
    let end_bound: int = main.len() - sub.len();
    
    let mut i: int = 0;
    
    while i <= end_bound
        invariant
            0 <= i <= end_bound + 1,
            end_bound == main.len() - sub.len(),
            sub.len() <= main.len(),
            sub.len() > 0,
            end_bound >= 0,
            forall|j: int| 0 <= j < i ==> sub != main.subrange(j, j + sub.len())
    {
        if sub == main.subrange(i, i + sub.len()) {
            assert(0 <= i <= main.len() - sub.len());
            assert(sub == main.subrange(i, i + sub.len()));
            return true;
        }
        i = i + 1;
    }
    
    // When we exit the loop, we've checked all valid positions
    assert(forall|j: int| 0 <= j <= main.len() - sub.len() ==> sub != main.subrange(j, j + sub.len())) by {
        assert(forall|j: int| 0 <= j < i ==> sub != main.subrange(j, j + sub.len()));
        assert(i > end_bound);
        assert(end_bound == main.len() - sub.len());
        
        // Any j in the range [0, main.len() - sub.len()] is less than i
        assert(forall|j: int| 0 <= j <= end_bound ==> j < i);
    };
    
    // Since no position matched, the result is false
    assert(!(exists|j: int| 0 <= j <= main.len() - sub.len() && sub == main.subrange(j, j + sub.len()))) by {
        assert(forall|j: int| 0 <= j <= main.len() - sub.len() ==> sub != main.subrange(j, j + sub.len()));
    };
    
    false
}

}