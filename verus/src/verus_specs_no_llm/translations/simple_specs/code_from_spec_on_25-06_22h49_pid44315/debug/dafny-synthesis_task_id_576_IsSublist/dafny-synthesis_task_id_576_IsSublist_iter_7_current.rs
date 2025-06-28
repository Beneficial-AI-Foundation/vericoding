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
            assert(main.len() - sub.len() < 0);
        };
        return false;
    }
    
    if sub.len() == 0 {
        // Empty subsequence exists at position 0
        assert(0 <= 0 <= main.len() - sub.len());
        assert(sub == main.subrange(0, 0 + sub.len())) by {
            assert(sub.len() == 0);
            assert(main.subrange(0, 0) == Seq::<int>::empty());
        };
        return true;
    }
    
    let mut i: usize = 0;
    let end_bound: usize = (main.len() - sub.len()) as usize;
    
    while i <= end_bound
        invariant
            0 <= i <= end_bound + 1,
            end_bound == main.len() - sub.len(),
            sub.len() <= main.len(),
            sub.len() > 0,
            main.len() - sub.len() >= 0,
            forall|j: int| 0 <= j < i ==> sub != main.subrange(j, j + sub.len())
    {
        if sub == main.subrange(i as int, (i as int) + sub.len()) {
            assert(0 <= i <= main.len() - sub.len());
            assert(sub == main.subrange(i as int, (i as int) + sub.len()));
            return true;
        }
        i += 1;
    }
    
    // When we exit the loop, we've checked all valid positions
    assert(forall|j: int| 0 <= j <= main.len() - sub.len() ==> sub != main.subrange(j, j + sub.len())) by {
        // From loop invariant: forall j in [0, i) => sub != main.subrange(j, j + sub.len())
        assert(forall|j: int| 0 <= j < i ==> sub != main.subrange(j, j + sub.len()));
        // We exited because i > end_bound, so i >= end_bound + 1
        assert(i >= end_bound + 1);
        assert(end_bound == main.len() - sub.len());
        // Therefore i > main.len() - sub.len(), which means we checked all valid positions
        assert(i as int > main.len() - sub.len());
        // Since we checked [0, i) and i > main.len() - sub.len(), we checked [0, main.len() - sub.len()]
        assert(forall|j: int| 0 <= j <= main.len() - sub.len() ==> j < i);
    };
    
    // Since no position matched, the result is false
    assert(!(exists|i: int| 0 <= i <= main.len() - sub.len() && sub == main.subrange(i, i + sub.len())));
    
    false
}

}