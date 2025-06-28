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
        return false;
    }
    
    if sub.len() == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    let end_bound = main.len() - sub.len();
    
    while i <= end_bound
        invariant
            0 <= i <= end_bound + 1,
            end_bound == main.len() - sub.len(),
            sub.len() <= main.len(),
            sub.len() > 0,
            forall|j: int| 0 <= j < i ==> sub != main.subrange(j, j + sub.len())
    {
        if sub == main.subrange(i as int, i as int + sub.len()) {
            assert(0 <= i <= main.len() - sub.len());
            assert(sub == main.subrange(i as int, i as int + sub.len()));
            return true;
        }
        i += 1;
    }
    
    // When we exit the loop, we've checked all valid positions
    assert(forall|j: int| 0 <= j <= main.len() - sub.len() ==> sub != main.subrange(j, j + sub.len())) by {
        assert(forall|j: int| 0 <= j < i ==> sub != main.subrange(j, j + sub.len()));
        assert(i == end_bound + 1);
        assert(end_bound == main.len() - sub.len());
        assert(forall|j: int| 0 <= j <= end_bound ==> sub != main.subrange(j, j + sub.len()));
    }
    
    false
}

}