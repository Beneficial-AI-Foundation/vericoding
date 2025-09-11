/* Check if strings in array end with given suffixes
Specification: endswith returns boolean array indicating which strings end with corresponding suffixes
Returns a boolean array which is True where the string element in a ends with suffix, otherwise False */

use vstd::prelude::*;

verus! {
fn endswith(a: Vec<&str>, suffix: Vec<&str>) -> (result: Vec<bool>)
    requires a.len() == suffix.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            result[i] == a[i].ends_with(suffix[i]) &&
            (result[i] == true ==> suffix[i].len() <= a[i].len()) &&
            (result[i] == false ==> 
                suffix[i].len() > a[i].len() || 
                !a[i].ends_with(suffix[i]))
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}