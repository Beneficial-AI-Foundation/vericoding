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
        assert(main.len() - sub.len() < 0);
        assert(forall|i: int| 0 <= i <= main.len() - sub.len() ==> false) by {
            assert(main.len() - sub.len() < 0);
            assert(forall|i: int| 0 <= i ==> i > main.len() - sub.len());
        };
        assert(!(exists|i: int| 0 <= i <= main.len() - sub.len() && sub == main.subrange(i, i + sub.len())));
        return false;
    }
    
    if sub.len() == 0 {
        // Empty subsequence exists at position 0
        assert(main.len() - sub.len() >= 0);
        assert(0 <= 0 <= main.len() - sub.len());
        assert(sub == main.subrange(0, 0 + sub.len())) by {
            assert(sub.len() == 0);
            assert(main.subrange(0, 0) == Seq::<int>::empty());
            assert(sub == Seq::<int>::empty());
        };
        assert(exists|i: int| 0 <= i <= main.len() - sub.len() && sub == main.subrange(i, i + sub.len())) by {
            assert(0 <= 0 <= main.len() - sub.len() && sub == main.subrange(0, 0 + sub.len()));
        };
        return true;
    }
    
    // At this point: sub.len() > 0 and sub.len() <= main.len()
    assert(sub.len() > 0);
    assert(sub.len() <= main.len());
    assert(main.len() - sub.len() >= 0);
    
    let mut i: int = 0;
    let end_bound: int = main.len() - sub.len();
    
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
            assert(exists|k: int| 0 <= k <= main.len() - sub.len() && sub == main.subrange(k, k + sub.len())) by {
                assert(0 <= i <= main.len() - sub.len() && sub == main.subrange(i, i + sub.len()));
            };
            return true;
        }
        i += 1;
    }
    
    // When we exit the loop, we've checked all valid positions
    assert(i > end_bound);
    assert(i >= end_bound + 1);
    assert(forall|j: int| 0 <= j < i ==> sub != main.subrange(j, j + sub.len()));
    
    assert(forall|j: int| 0 <= j <= main.len() - sub.len() ==> sub != main.subrange(j, j + sub.len())) by {
        assert(forall|j: int| 0 <= j < i ==> sub != main.subrange(j, j + sub.len()));
        assert(i >= end_bound + 1);
        assert(end_bound == main.len() - sub.len());
        assert(i >= main.len() - sub.len() + 1);
        
        // For any j in [0, main.len() - sub.len()], we have j < i, so the property holds
        assert(forall|j: int| 0 <= j <= main.len() - sub.len() ==> j <= end_bound);
        assert(forall|j: int| 0 <= j <= end_bound ==> j < i);
    };
    
    // Since no position matched, the result is false
    assert(!(exists|i: int| 0 <= i <= main.len() - sub.len() && sub == main.subrange(i, i + sub.len()))) by {
        assert(forall|j: int| 0 <= j <= main.len() - sub.len() ==> sub != main.subrange(j, j + sub.len()));
    };
    
    false
}

}