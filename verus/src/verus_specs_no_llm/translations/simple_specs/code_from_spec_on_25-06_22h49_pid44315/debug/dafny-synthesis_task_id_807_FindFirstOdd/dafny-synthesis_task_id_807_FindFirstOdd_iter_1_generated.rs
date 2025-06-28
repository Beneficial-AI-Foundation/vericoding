use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsOdd(x: int) -> bool {
    x % 2 != 0
}

fn FindFirstOdd(a: Vec<int>) -> (found: bool, index: int)
    ensures
        !found ==> forall|i: int| 0 <= i < a.len() ==> !IsOdd(a.spec_index(i)),
        found ==> 0 <= index < a.len() && IsOdd(a.spec_index(index)) && forall|i: int| 0 <= i < index ==> !IsOdd(a.spec_index(i))
{
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> !IsOdd(a.spec_index(j))
    {
        if IsOdd(a[i]) {
            return (true, i);
        }
        i = i + 1;
    }
    
    (false, 0)
}

}

The implementation:

   - Iterates through the vector with index `i`
   - Maintains a loop invariant that all elements before index `i` are even
   - When an odd element is found, immediately returns `(true, i)`
   - If the loop completes without finding an odd element, returns `(false, 0)`

The loop invariant `forall|j: int| 0 <= j < i ==> !IsOdd(a.spec_index(j))` ensures that when we exit the loop (either by finding an odd number or reaching the end), we can prove the postconditions about all previous elements being even.