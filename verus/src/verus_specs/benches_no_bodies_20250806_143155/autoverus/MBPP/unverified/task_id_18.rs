use vstd::prelude::*;

fn main() {}

verus! {

fn contains(str: &[u8], key: u8) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    return false;  // TODO: Remove this line and implement the function body
}

fn remove_chars(str1: &[u8], str2: &[u8]) -> (result: Vec<u8>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                #[trigger] str1[i],
            )),
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!
