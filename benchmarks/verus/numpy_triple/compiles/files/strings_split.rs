/* For each element in a vector of strings, return a list of the words in the string, using sep as the delimiter string.

Specification: split returns a vector where each string is split into a list of substrings based on the separator, with proper handling of maxsplit constraints and reconstruction properties. */

use vstd::prelude::*;

verus! {
fn split(a: &Vec<String>, sep: &String, maxsplit: Option<usize>) -> (result: Vec<Vec<String>>)
    requires sep@.len() > 0,
    ensures
        result.len() == a.len(),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}