/* For each element in a vector, return a copy with the trailing characters removed.

Specification: numpy.strings.rstrip removes trailing characters from each string in the vector.
    
rstrip removes trailing characters from the end of each string. If chars is None, 
whitespace characters are removed. If chars is provided, any combination of those 
characters is removed from the end.
    
Mathematical Properties:
1. Element-wise transformation: Each string is processed independently
2. Trailing character removal: Only characters at the end are removed
3. Maximal stripping: Remove as many trailing characters as possible
4. Character set filtering: Only characters in the specified set are removed
5. Whitespace default: When chars is None, whitespace characters are removed
    
From NumPy documentation:
- Parameters: a (array_like) - Input array with string dtype
              chars (optional) - Characters to remove, whitespace if None
- Returns: out (ndarray) - Output array with trailing characters removed */

use vstd::prelude::*;

verus! {
fn rstrip(a: &Vec<String>, chars: Option<&Vec<char>>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            #[trigger] result[i]@.len() <= #[trigger] a[i]@.len(),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}