/* A new 1-D array initialized from text data in a string

Specification: fromstring parses a string into a vector of floats using a separator */

use vstd::prelude::*;

verus! {
fn fromstring(input: Vec<char>, sep: Vec<char>) -> (result: Vec<f32>)
    requires
        sep.len() > 0,
        input.len() > 0,
    ensures
        result.len() > 0,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}