use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SumArray(xs: Vec<int>) -> (s: int)
    ensures
        s == Sum(xs.spec_index(..))
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            sum == Sum(xs.spec_index(..i as int))
    {
        sum = sum + xs[i];
        i = i + 1;
    }
    
    sum
}

}

The implementation works as follows:

   - `0 <= i <= xs.len()` ensures the index is within bounds
   - `sum == Sum(xs.spec_index(..i as int))` maintains that our accumulated sum equals the sum of the first `i` elements

The key insight is that `Sum(xs.spec_index(..i as int))` represents the sum of elements from index 0 to i-1, and when we add `xs[i]`, we get `Sum(xs.spec_index(..(i+1) as int))`. At the end of the loop, this becomes the sum of the entire array.