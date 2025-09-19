// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn determine_media_types(associations: Vec<(String, String)>, filenames: Vec<String>) -> (result: Vec<String>)
    ensures 
        result.len() == filenames.len(),
        associations.len() == 0 ==> 
            forall|i: int| 0 <= i < result.len() ==> result[i]@ == "unknown"@
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}