// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): use @ operator for string comparison */
    if category@ == "Character"@ {
        Some("S1")
    } else if category@ == "Integer"@ {
        Some("bhilqnp")
    } else if category@ == "UnsignedInteger"@ {
        Some("BHILQNP")
    } else if category@ == "Float"@ {
        Some("fdg")
    } else if category@ == "Complex"@ {
        Some("FDG")
    } else if category@ == "AllInteger"@ {
        Some("bBhHiIlLqQnNpP")
    } else if category@ == "AllFloat"@ {
        Some("fdgFDG")
    } else if category@ == "Datetime"@ {
        Some("Mm")
    } else if category@ == "All"@ {
        Some("?bhilqnpBHILQNPfdgFDGSUVOMm")
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}