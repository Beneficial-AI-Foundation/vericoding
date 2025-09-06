/* For each element in a vector, return a list of the words in the string, using sep as the delimiter string.
Splits from the right, meaning that splits are made from the right side of the string.

Specification: rsplit splits each string in the vector from the right using the given separator.
The resulting vector contains lists of strings where each list represents the split parts
of the corresponding input string. */

use vstd::prelude::*;

verus! {
fn rsplit(a: &Vec<String>, sep: &str, maxsplit: usize) -> (result: Vec<Vec<String>>)
    requires sep@.len() > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i].len() > 0,
        maxsplit == 0 ==> forall|i: int| 0 <= i < a.len() ==> result[i].len() == 1 && result[i][0]@ == a[i]@,
        forall|i: int| 0 <= i < a.len() ==> result[i].len() <= maxsplit + 1,
        forall|i: int| 0 <= i < a.len() ==> a[i]@.len() == 0 ==> result[i].len() == 1 && result[i][0]@ == a[i]@,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}