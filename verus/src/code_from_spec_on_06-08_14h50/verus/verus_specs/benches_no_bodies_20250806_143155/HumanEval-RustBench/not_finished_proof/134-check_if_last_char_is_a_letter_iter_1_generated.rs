use vstd::prelude::*;

verus! {

pub spec fn is_alphabetic(c: char) -> (result: bool);
// pure-end

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_alphabetic)]
fn ex_is_alphabetic(c: char) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (c.is_alphabetic()),
    // post-conditions-end
{
    c.is_alphabetic()
}

pub spec fn is_whitespace(c: char) -> (result: bool);
// pure-end

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(is_whitespace)]
fn ex_is_whitespace(c: char) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (c.is_whitespace()),
    // post-conditions-end
{
    c.is_whitespace()
}

fn check_if_last_char_is_a_letter(txt: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (txt@.len() > 0 && txt@.last().is_alphabetic() && (txt@.len() == 1
            || txt@.index(txt@.len() - 2).is_whitespace())),
    // post-conditions-end
{
    if txt@.len() == 0 {
        return false;
    }
    
    let last_char = txt@.last();
    if !last_char.is_alphabetic() {
        return false;
    }
    
    if txt@.len() == 1 {
        return true;
    }
    
    let second_last_char = txt@.index(txt@.len() - 2);
    second_last_char.is_whitespace()
}

}
fn main() {}