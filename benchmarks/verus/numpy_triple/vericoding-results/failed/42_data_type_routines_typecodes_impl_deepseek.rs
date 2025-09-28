// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_str_eq(a: &str, b: &str) -> bool {
    a@ == b@
}

proof fn lemma_str_ne(a: &str, b: &str) -> bool {
    a@ != b@
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
    /* code modified by LLM (iteration 5): Using manual string comparison with string view comparisons */
    if lemma_str_eq(category, "Character") {
        Some("S1")
    } else if lemma_str_eq(category, "Integer") {
        Some("bhilqnp")
    } else if lemma_str_eq(category, "UnsignedInteger") {
        Some("BHILQNP")
    } else if lemma_str_eq(category, "Float") {
        Some("fdg")
    } else if lemma_str_eq(category, "Complex") {
        Some("FDG")
    } else if lemma_str_eq(category, "AllInteger") {
        Some("bBhHiIlLqQnNpP")
    } else if lemma_str_eq(category, "AllFloat") {
        Some("fdgFDG")
    } else if lemma_str_eq(category, "Datetime") {
        Some("Mm")
    } else if lemma_str_eq(category, "All") {
        Some("?bhilqnpBHILQNPfdgFDGSUVOMm")
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}