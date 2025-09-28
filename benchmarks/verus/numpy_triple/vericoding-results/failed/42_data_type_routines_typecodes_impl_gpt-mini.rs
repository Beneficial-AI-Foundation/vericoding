// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compare two &str by comparing their sequence views */
fn is_eq(a: &str, b: &str) -> (res: bool)
    ensures
        res == (a@ == b@),
{
    let res = a@ == b@;
    res
}
// </vc-helpers>

// <vc-spec>
fn typecodes(category: &str) -> (result: Option<&str>)
    ensures
        (category@ == "Character"@) ==> (result == Some("S1")),
        (category@ == "Integer"@) ==> (result == Some("bhilqnp")),
        (category@ == "UnsignedInteger"@) ==> (result == Some("BHILQNP")),
        (category@ == "Float"@) ==> (result == Some("fdg")),
        (category@ == "Complex"@) ==> (result == Some("FDG")),
        (category@ == "AllInteger"@) ==> (result == Some("bBhHiIlLqQnNpP")),
        (category@ == "AllFloat"@) ==> (result == Some("fdgFDG")),
        (category@ == "Datetime"@) ==> (result == Some("Mm")),
        (category@ == "All"@) ==> (result == Some("?bhilqnpBHILQNPfdgFDGSUVOMm")),
        (category@ != "Character"@ && category@ != "Integer"@ && category@ != "UnsignedInteger"@ && 
         category@ != "Float"@ && category@ != "Complex"@ && category@ != "AllInteger"@ && 
         category@ != "AllFloat"@ && category@ != "Datetime"@ && category@ != "All"@) ==> (result == None::<&str>)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return appropriate typecode strings based on category using is_eq helper */
    if is_eq(category, "Character") {
        Some("S1")
    } else if is_eq(category, "Integer") {
        Some("bhilqnp")
    } else if is_eq(category, "UnsignedInteger") {
        Some("BHILQNP")
    } else if is_eq(category, "Float") {
        Some("fdg")
    } else if is_eq(category, "Complex") {
        Some("FDG")
    } else if is_eq(category, "AllInteger") {
        Some("bBhHiIlLqQnNpP")
    } else if is_eq(category, "AllFloat") {
        Some("fdgFDG")
    } else if is_eq(category, "Datetime") {
        Some("Mm")
    } else if is_eq(category, "All") {
        Some("?bhilqnpBHILQNPfdgFDGSUVOMm")
    } else {
        None::<&str>
    }
}
// </vc-code>

}
fn main() {}