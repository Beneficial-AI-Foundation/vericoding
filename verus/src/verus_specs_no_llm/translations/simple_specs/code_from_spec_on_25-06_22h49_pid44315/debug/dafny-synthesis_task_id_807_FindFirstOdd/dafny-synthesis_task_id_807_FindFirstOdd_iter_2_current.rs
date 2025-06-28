use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsOdd(x: int) -> bool {
    x % 2 != 0
}

// Executable version of IsOdd for use in the implementation
fn is_odd_exec(x: int) -> (result: bool)
    ensures result == IsOdd(x)
{
    x % 2 != 0
}

fn FindFirstOdd(a: Vec<int>) -> (found: bool, index: int)
    ensures
        !found ==> forall|i: int| 0 <= i < a.len() ==> !IsOdd(a.spec_index(i)),
        found ==> 0 <= index < a.len() && IsOdd(a.spec_index(index)) && forall|i: int| 0 <= i < index ==> !IsOdd(a.spec_index(i))
{
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> !IsOdd(a.spec_index(j))
    {
        if is_odd_exec(a[i]) {
            // Add proof assertions to help Verus verify the postconditions
            assert(IsOdd(a.spec_index(i as int)));
            assert(forall|j: int| 0 <= j < i ==> !IsOdd(a.spec_index(j)));
            return (true, i as int);
        }
        i = i + 1;
    }
    
    // At this point, we've checked all elements and none are odd
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> !IsOdd(a.spec_index(j)));
    
    (false, 0)
}

}