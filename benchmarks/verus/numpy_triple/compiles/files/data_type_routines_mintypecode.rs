/* 
{
  "name": "numpy.mintypecode",
  "category": "Miscellaneous Type Utilities",
  "description": "Return the character for the minimum-size type to which given types can be safely cast",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.mintypecode.html",
  "doc": "Return the character for the minimum-size type to which given types can be safely cast.\n\nParameters\n----------\ntypechars : list of str or array_like\n    If a list of strings, each string should represent a dtype. If array_like, the character representation of the array dtype is used.\ntypeset : str or list of str, optional\n    The set of characters that the returned character is chosen from. The default set is 'GDFgdf'.\ndefault : str, optional\n    The default character if none in typeset matches.\n\nReturns\n-------\ntypechar : str\n    The character representing the minimum-size type found.\n\nExamples\n--------\n>>> np.mintypecode(['d', 'f', 'S'])\n'd'\n>>> x = np.array([1.1, 2-3.j])\n>>> np.mintypecode(x)\n'D'\n>>> np.mintypecode('abceh', default='G')\n'G'"
}
*/

/* Return the character for the minimum-size type to which given types can be safely cast */

/* Specification: mintypecode returns the minimum-size type character that can handle all input types */
use vstd::prelude::*;

verus! {

/* NumPy type character to precedence mapping based on the default typeset 'GDFgdf'
   Lower values indicate higher precedence (smaller/more restrictive types) */
spec fn typechar_precedence(c: char) -> nat {
    match c {
        'g' => 0,  // longdouble (most restrictive in numerical sense)
        'd' => 1,  // double
        'f' => 2,  // float
        'F' => 3,  // csingle (complex float)
        'D' => 4,  // cdouble (complex double)
        'G' => 5,  // clongdouble (complex long double)
        _ => 6,    // other types (lowest precedence)
    }
}

/* Check if a type character is in the given typeset */
spec fn char_in_typeset(c: char, typeset: Seq<char>) -> bool {
    typeset.contains(c)
}
// <vc-helpers>
// </vc-helpers>
fn mintypecode(typechars: Vec<char>, typeset: Vec<char>, default: char) -> (result: char)
    requires typeset@ == seq!['G', 'D', 'F', 'g', 'd', 'f'],
// <vc-implementation>
{
    return 'g'; // TODO: Remove this line and implement the function body
}
// </vc-implementation>
spec fn mintypecode_specification(typechars: Seq<char>, typeset: Seq<char>, default: char) -> bool 
    recommends typeset == seq!['G', 'D', 'F', 'g', 'd', 'f']
{
    let result = 'g'; // This would be the actual result in real implementation
    
    // Case 1: No input types in typeset - return default
    (forall |c: char| #![auto] typechars.contains(c) && !char_in_typeset(c, typeset) ==> result == default) &&
    
    // Case 2: Special rule - if both 'F' and 'd' are in intersection, return 'D'
    ({
        let intersection = typechars.filter(|c: char| char_in_typeset(c, typeset));
        intersection.len() > 0 && intersection.contains('F') && intersection.contains('d') ==> result == 'D'
    }) &&
    
    // Case 3: Normal case - return minimum precedence type from intersection
    ({
        let intersection = typechars.filter(|c: char| char_in_typeset(c, typeset));
        intersection.len() > 0 && !(intersection.contains('F') && intersection.contains('d')) ==>
        intersection.contains(result) && 
        forall |c: char| #![auto] intersection.contains(c) ==> typechar_precedence(result) <= typechar_precedence(c)
    }) &&
    
    // Validity: result is either from intersection or default
    ({
        let intersection = typechars.filter(|c: char| char_in_typeset(c, typeset));
        intersection.contains(result) || result == default
    }) &&
    
    // Safety property: result can handle all input types
    (forall |c: char| #![auto] typechars.contains(c) && char_in_typeset(c, typeset) ==> 
      typechar_precedence(result) <= typechar_precedence(c) || 
      (result == 'D' && typechars.contains('F') && typechars.contains('d')))
}

proof fn mintypecode_spec(typechars: Vec<char>, typeset: Vec<char>, default: char)
    requires typeset@ == seq!['G', 'D', 'F', 'g', 'd', 'f'],
    ensures mintypecode_specification(typechars@, typeset@, default)
// <vc-proof>
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-proof>

fn main() {
}

}