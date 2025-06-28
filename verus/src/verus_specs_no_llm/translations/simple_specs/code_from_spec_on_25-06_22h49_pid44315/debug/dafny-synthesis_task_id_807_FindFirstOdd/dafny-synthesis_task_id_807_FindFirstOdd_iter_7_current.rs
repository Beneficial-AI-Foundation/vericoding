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
            // Proof that we found an odd element at position i
            proof {
                assert(0 <= i < a.len());
                assert(IsOdd(a.spec_index(i as int))) by {
                    // The postcondition of is_odd_exec gives us what we need
                    assert(is_odd_exec(a[i]) == IsOdd(a[i] as int));
                    assert(a[i] as int == a.spec_index(i as int));
                };
                // The invariant already gives us the forall condition
            }
            return (true, i);
        }
        
        // Update invariant for next iteration
        proof {
            assert(!IsOdd(a.spec_index(i as int))) by {
                assert(!is_odd_exec(a[i]));
                assert(!is_odd_exec(a[i]) == !IsOdd(a[i] as int));
                assert(a[i] as int == a.spec_index(i as int));
            };
            // This helps maintain the invariant for the extended range
            assert(forall|j: int| 0 <= j < (i + 1) ==> !IsOdd(a.spec_index(j))) by {
                assert(forall|j: int| 0 <= j < i ==> !IsOdd(a.spec_index(j))); // from invariant
                assert(!IsOdd(a.spec_index(i as int))); // just proved above
            };
        }
        
        i = i + 1;
    }
    
    // All elements checked, none are odd
    proof {
        assert(i == a.len());
        assert(forall|j: int| 0 <= j < a.len() ==> !IsOdd(a.spec_index(j))) by {
            // The invariant gives us this since i == a.len()
        };
    }
    
    (false, 0)
}

}