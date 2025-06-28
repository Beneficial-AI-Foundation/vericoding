use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsOdd(x: int) -> bool {
    x % 2 != 0
}

// Executable version of IsOdd for use in the implementation
fn is_odd_exec(x: i32) -> (result: bool)
    ensures result == IsOdd(x as int)
{
    x % 2 != 0
}

fn FindFirstOdd(a: Vec<i32>) -> (result: (bool, usize))
    ensures
        !result.0 ==> forall|i: int| 0 <= i < a.len() ==> !IsOdd(a.spec_index(i)),
        result.0 ==> 0 <= result.1 < a.len() && IsOdd(a.spec_index(result.1 as int)) && forall|i: int| 0 <= i < result.1 ==> !IsOdd(a.spec_index(i))
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> !IsOdd(a.spec_index(j))
    {
        if is_odd_exec(a[i]) {
            // Proof assertions to establish the postconditions
            assert(0 <= i < a.len());
            assert(IsOdd(a.spec_index(i as int))) by {
                assert(a[i] == a.spec_index(i as int));
            };
            assert(forall|j: int| 0 <= j < i ==> !IsOdd(a.spec_index(j)));
            return (true, i);
        }
        
        // Strengthen the invariant for the next iteration
        assert(!IsOdd(a.spec_index(i as int))) by {
            assert(a[i] == a.spec_index(i as int));
            assert(!is_odd_exec(a[i]));
        };
        
        i = i + 1;
    }
    
    // At this point, we've checked all elements and none are odd
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> !IsOdd(a.spec_index(j))) by {
        assert(forall|j: int| 0 <= j < i ==> !IsOdd(a.spec_index(j)));
        assert(i == a.len());
    };
    
    (false, 0)
}

}