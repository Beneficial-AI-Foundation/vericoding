/* A new 1-D array initialized from text data in a string */

use vstd::prelude::*;

verus! {
fn fromstring(input: &str, sep: &str, n: usize) -> (result: Vec<f64>)
    requires 
        n > 0,
        sep@ != ""@,
    ensures
        result.len() == n,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}