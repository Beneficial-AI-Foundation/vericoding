/* Return (a * i), that is string multiple concatenation, element-wise.
Values in i of less than 0 are treated as 0 (which yields an empty string).

Specification: multiply performs element-wise string repetition.
Each output string is the corresponding input string repeated the specified number of times.
Negative repetition counts produce empty strings. This comprehensive specification
captures the core mathematical properties of string multiplication in NumPy. */

use vstd::prelude::*;

verus! {
spec fn repeat_string(s: &str, count: int) -> String
    decreases count
{
    if count <= 0 {
        String::new()
    } else {
        s.to_string() + repeat_string(s, count - 1)
    }
}
fn multiply(a: Vec<String>, i: Vec<i32>) -> (result: Vec<String>)
    requires a.len() == i.len(),
    ensures 
        result.len() == a.len(),
        forall|j: int| 0 <= j < result.len() ==> 
            result[j] == repeat_string(&a[j], i[j] as int),
        forall|j: int| 0 <= j < result.len() && i[j] <= 0 ==> 
            result[j] == String::new(),
        forall|j: int| 0 <= j < result.len() && i[j] == 1 ==> 
            result[j] == a[j],
        forall|j: int| 0 <= j < result.len() && i[j] == 0 ==> 
            result[j] == String::new(),
        forall|j: int| 0 <= j < result.len() && a[j] == String::new() ==> 
            result[j] == String::new()
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}