// <vc-preamble>
datatype StringOption = None | Some(s: string)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): renamed to avoid duplicate with method */
function getTypecodes(category: string): StringOption {
  if category == "Character" then Some("S1")
  else if category == "Integer" then Some("bhilqnp")
  else if category == "UnsignedInteger" then Some("BHILQNP")
  else if category == "Float" then Some("fdg")
  else if category == "Complex" then Some("FDG")
  else if category == "AllInteger" then Some("bBhHiIlLqQnNpP")
  else if category == "AllFloat" then Some("fdgFDG")
  else if category == "Datetime" then Some("Mm")
  else if category == "All" then Some("?bhilqnpBHILQNPfdgFDGSUVOMm")
  else None
}
// </vc-helpers>

// <vc-spec>
method typecodes(category: string) returns (result: StringOption)
    // Returns type character codes for valid NumPy dtype categories
    ensures category == "Character" ==> result == Some("S1")
    ensures category == "Integer" ==> result == Some("bhilqnp")  
    ensures category == "UnsignedInteger" ==> result == Some("BHILQNP")
    ensures category == "Float" ==> result == Some("fdg")
    ensures category == "Complex" ==> result == Some("FDG")
    ensures category == "AllInteger" ==> result == Some("bBhHiIlLqQnNpP")
    ensures category == "AllFloat" ==> result == Some("fdgFDG")
    ensures category == "Datetime" ==> result == Some("Mm")
    ensures category == "All" ==> result == Some("?bhilqnpBHILQNPfdgFDGSUVOMm")
    // Returns None for unrecognized categories
    ensures (category != "Character" && category != "Integer" && category != "UnsignedInteger" && 
            category != "Float" && category != "Complex" && category != "AllInteger" && 
            category != "AllFloat" && category != "Datetime" && category != "All") ==> result == None
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): call renamed helper function */
{
  result := getTypecodes(category);
}
// </vc-code>
