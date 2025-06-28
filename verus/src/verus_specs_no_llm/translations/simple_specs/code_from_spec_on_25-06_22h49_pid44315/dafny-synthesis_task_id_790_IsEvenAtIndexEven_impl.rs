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
        // For negative numbers, we use the mathematical property that
        // n is even iff -n is even
        let abs_n = -n;
        proof {
            // Prove that n % 2 == 0 <==> (-n) % 2 == 0
            assert(IsEven(n) <==> IsEven(-n)) by(nonlinear_arith);
            assert(abs_n >= 0);
        }
        is_even_exec(abs_n as usize)
    }
}

fn is_even_at_index_even(lst: Seq<int>) -> (result: bool)
    ensures
        result <==> forall|i: int| 0 <= i < lst.len() ==> (IsEven(i) ==> IsEven(lst[i]))
{
    let mut index: usize = 0;
    
    while index < lst.len()
        invariant
            0 <= index <= lst.len(),
            forall|i: int| 0 <= i < index ==> (IsEven(i) ==> IsEven(lst[i]))
    {
        if is_even_exec(index) {
            // If index is even, check if lst[index] is also even
            let val = lst[index as int];
            if !is_even_int(val) {
                // We found a counterexample: index is even but lst[index] is not even
                proof {
                    assert(IsEven(index as int));
                    assert(!IsEven(lst[index as int]));
                    assert(0 <= index < lst.len());
                    // This shows the negation of our target property
                    assert(exists|i: int| 0 <= i < lst.len() && IsEven(i) && !IsEven(lst[i])) by {
                        assert(0 <= index as int < lst.len() && IsEven(index as int) && !IsEven(lst[index as int]));
                    }
                    // Therefore the universal quantification is false
                    assert(!(forall|i: int| 0 <= i < lst.len() ==> (IsEven(i) ==> IsEven(lst[i]))));
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
        assert(forall|i: int| 0 <= i < index as int ==> (IsEven(i) ==> IsEven(lst[i])));
        // Since index == lst.len(), we have index as int == lst.len()
        assert(index as int == lst.len());
        assert(forall|i: int| 0 <= i < lst.len() ==> (IsEven(i) ==> IsEven(lst[i])));
    }
    return true;
}

}