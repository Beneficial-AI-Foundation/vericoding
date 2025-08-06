use vstd::prelude::*;

fn main() {}

verus! {

fn contains(str: &[u8], key: u8) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    for i in 0..str.len()
        invariant
            forall|j: int| 0 <= j < i ==> str[j] != key,
    {
        if str[i] == key {
            return true;
        }
    }
    false
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
    let mut result = Vec::new();
    
    for i in 0..str1.len()
        invariant
            forall|j: int|
                0 <= j < result.len() ==> (str1@.contains(#[trigger] result[j]) && !str2@.contains(
                    #[trigger] result[j],
                )),
            forall|j: int|
                0 <= j < i ==> (str2@.contains(#[trigger] str1[j]) || result@.contains(
                    #[trigger] str1[j],
                )),
    {
        let ch = str1[i];
        if !contains(str2, ch) {
            result.push(ch);
        }
    }
    
    result
}

} // verus!