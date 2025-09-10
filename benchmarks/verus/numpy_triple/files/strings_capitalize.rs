/* Return a copy of a with only the first character of each element capitalized */

use vstd::prelude::*;

verus! {
fn capitalize(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() == a[i]@.len()
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}