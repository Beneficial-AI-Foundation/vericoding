// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn improve_product_name(s: String, c: String) -> (result: String)
    requires
        s@.len() >= 2,
        c@.len() >= 1,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "---".to_string()
    // impl-end
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // println!("{}", improve_product_name("AZAMON".to_string(), "APPLE".to_string()));
    // println!("{}", improve_product_name("AZAMON".to_string(), "AAAAAAAAAAALIBABA".to_string()));
    // println!("{}", improve_product_name("APPLE".to_string(), "BANANA".to_string()));
}