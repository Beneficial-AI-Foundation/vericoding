use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

spec fn IsOdd(n: int) -> bool {
    n % 2 != 0
}

fn FirstEvenOddDifference(a: Vec<int>) -> (diff: int)
    requires
        a.len() >= 2,
        exists i :: 0 <= i < a.len() && IsEven(a.spec_index(i)),
        exists i :: 0 <= i < a.len() && IsOdd(a.spec_index(i))
    ensures
        exists i, j :: 0 <= i < a.len() && 0 <= j < a.len() && IsEven(a.spec_index(i)) && IsOdd(a.spec_index(j)) && diff == a.spec_index(i) - a.spec_index(j) && 
    (forall k :: 0 <= k < i ==> IsOdd(a.spec_index(k))) && (forall k :: 0 <= k < j ==> IsEven(a.spec_index(k)))
{
    let mut first_even_idx: usize = 0;
    let mut first_odd_idx: usize = 0;
    
    // Find first even number
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall k :: 0 <= k < i ==> IsOdd(a.spec_index(k))
    {
        if IsEven(a[i]) {
            first_even_idx = i;
            break;
        }
        i += 1;
    }
    
    // Find first odd number
    let mut j = 0;
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            forall k :: 0 <= k < j ==> IsEven(a.spec_index(k))
    {
        if IsOdd(a[j]) {
            first_odd_idx = j;
            break;
        }
        j += 1;
    }
    
    a[first_even_idx] - a[first_odd_idx]
}

}