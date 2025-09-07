/* Check if strings in array start with given prefixes. Returns a boolean array which is True where the string element in a starts with prefix, otherwise False. */

use vstd::prelude::*;

verus! {
fn startswith(a: Vec<String>, prefixes: Vec<String>) -> (result: Vec<bool>)
    requires a.len() == prefixes.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> (
            result[i] == a[i]@.starts_with(prefixes[i]@) &&
            (result[i] ==> 
                prefixes[i]@.len() <= a[i]@.len() &&
                a[i]@.subrange(0, prefixes[i]@.len() as int) == prefixes[i]@) &&
            (!result[i] ==> 
                prefixes[i]@.len() > a[i]@.len() ||
                a[i]@.subrange(0, prefixes[i]@.len() as int) != prefixes[i]@)
        ),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}