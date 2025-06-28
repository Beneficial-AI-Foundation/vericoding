use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

// Executable function to check if a number is even
fn is_even_exec(n: usize) -> (result: bool)
    ensures result <==> IsEven(n as int)
{
    n % 2 == 0
}

// Helper function to check if an integer is even (for potentially negative values)
fn is_even_int(n: int) -> (result: bool)
    ensures result <==> IsEven(n)
{
    if n >= 0 {
        is_even_exec(n as usize)
    } else {
        // For negative numbers, use the mathematical property that 
        // n is even iff -n is even
        let pos_n = -n;
        is_even_exec(pos_n as usize)
    }
}

fn is_even_at_index_even(lst: Seq<int>) -> (result: bool)
    ensures
        result <==> forall|i: int| 0 <= i < lst.len() ==> (IsEven(i) ==> IsEven(lst.spec_index(i)))
{
    let mut index: usize = 0;
    
    while index < lst.len()
        invariant
            0 <= index <= lst.len(),
            forall|i: int| 0 <= i < index ==> (IsEven(i) ==> IsEven(lst.spec_index(i)))
    {
        if is_even_exec(index) {
            // If index is even, check if lst[index] is also even
            let val = lst[index as int];
            if !is_even_int(val) {
                // We found a counterexample: index is even but lst[index] is not even
                proof {
                    assert(IsEven(index as int));
                    assert(!IsEven(lst.spec_index(index as int)));
                    assert(0 <= index < lst.len());
                    // This contradicts the required property
                    assert(exists|i: int| 0 <= i < lst.len() && IsEven(i) && !IsEven(lst.spec_index(i)));
                }
                return false;
            }
        }
        index = index + 1;
    }
    
    // At this point, we've checked all indices from 0 to lst.len()-1
    // The loop invariant tells us that for all i in [0, index), the property holds
    // Since index == lst.len(), this means the property holds for all valid indices
    proof {
        assert(index == lst.len());
        assert(forall|i: int| 0 <= i < lst.len() ==> (IsEven(i) ==> IsEven(lst.spec_index(i))));
    }
    return true;
}

}