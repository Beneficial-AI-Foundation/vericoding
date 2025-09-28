// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Used `vstd::string::StrSlice::new` for string literals to enable comparison. */
fn typecodes_helper(category: &str) -> (result: Option<&str>)
    ensures
        (category@ == vstd::string::StrSlice::new("Character")@) ==> (result == Some("S1")),
        (category@ == vstd::string::StrSlice::new("Integer")@) ==> (result == Some("bhilqnp")),
        (category@ == vstd::string::StrSlice::new("UnsignedInteger")@) ==> (result == Some("BHILQNP")),
        (category@ == vstd::string::StrSlice::new("Float")@) ==> (result == Some("fdg")),
        (category@ == vstd::string::StrSlice::new("Complex")@) ==> (result == Some("FDG")),
        (category@ == vstd::string::StrSlice::new("AllInteger")@) ==> (result == Some("bBhHiIlLqQnNpP")),
        (category@ == vstd::string::StrSlice::new("AllFloat")@) ==> (result == Some("fdgFDG")),
        (category@ == vstd::string::StrSlice::new("Datetime")@) ==> (result == Some("Mm")),
        (category@ == vstd::string::StrSlice::new("All")@) ==> (result == Some("?bhilqnpBHILQNPfdgFDGSUVOMm")),
        (category@ != vstd::string::StrSlice::new("Character")@ && category@ != vstd::string::StrSlice::new("Integer")@ && category@ != vstd::string::StrSlice::new("UnsignedInteger")@ && 
         category@ != vstd::string::StrSlice::new("Float")@ && category@ != vstd::string::StrSlice::new("Complex")@ && category@ != vstd::string::StrSlice::new("AllInteger")@ && 
         category@ != vstd::string::StrSlice::new("AllFloat")@ && category@ != vstd::string::StrSlice::new("Datetime")@ && category@ != vstd::string::StrSlice::new("All")@) ==> (result == None::<&str>)
{
    if category@ == vstd::string::StrSlice::new("Character")@ {
        Some("S1")
    } else if category@ == vstd::string::StrSlice::new("Integer")@ {
        Some("bhilqnp")
    } else if category@ == vstd::string::StrSlice::new("UnsignedInteger")@ {
        Some("BHILQNP")
    } else if category@ == vstd::string::StrSlice::new("Float")@ {
        Some("fdg")
    } else if category@ == vstd::string::StrSlice::new("Complex")@ {
        Some("FDG")
    } else if category@ == vstd::string::StrSlice::new("AllInteger")@ {
        Some("bBhHiIlLqQnNpP")
    } else if category@ == vstd::string::StrSlice::new("AllFloat")@ {
        Some("fdgFDG")
    } else if category@ == vstd::string::StrSlice::new("Datetime")@ {
        Some("Mm")
    } else if category@ == vstd::string::StrSlice::new("All")@ {
        Some("?bhilqnpBHILQNPfdgFDGSUVOMm")
    } else {
        None
    }
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
/* code modified by LLM (iteration 5): Modified `typecodes` function to return `typecodes_helper(category)` */
{
    typecodes_helper(category)
}
// </vc-code>

}
fn main() {}