use vstd::prelude::*;

verus! {

pub open spec fn is_alphabetic(c: char) -> (result: bool)
{
    /* code modified by LLM (iteration 2): Fixed spec function visibility and replaced uninterp with arbitrary */
    arbitrary()
}
// pure-end

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_alphabetic)]
pub fn ex_is_alphabetic(c: char) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (c.is_alphabetic()),
    // post-conditions-end
{
    /* code modified by LLM (iteration 3): Added pub visibility to match spec function visibility */
    c.is_alphabetic()
}

pub open spec fn is_whitespace(c: char) -> (result: bool)
{
    /* code modified by LLM (iteration 2): Fixed spec function visibility and replaced uninterp with arbitrary */
    arbitrary()
}
// pure-end

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_whitespace)]
pub fn ex_is_whitespace(c: char) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (c.is_whitespace()),
    // post-conditions-end
{
    /* code modified by LLM (iteration 3): Added pub visibility to match spec function visibility */
    c.is_whitespace()
}

fn check_if_last_char_is_a_letter(txt: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (txt@.len() > 0 && txt@.last().is_alphabetic() && (txt@.len() == 1
            || txt@.index(txt@.len() - 2).is_whitespace())),
    // post-conditions-end
{
    /* code modified by LLM (iteration 2): Fixed implementation to use proper executable code and indexing */
    if txt.len() == 0 {
        return false;
    }
    
    let last_char = txt.chars().last().unwrap();
    if !last_char.is_alphabetic() {
        return false;
    }
    
    if txt.len() == 1 {
        return true;
    }
    
    let second_last_char = txt.chars().nth(txt.len() - 2).unwrap();
    second_last_char.is_whitespace()
}

}
fn main() {}