use vstd::prelude::*;

fn main() {}

verus! {

//ATOM
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

//IMPL remove_chars
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
        /* code modified by LLM (iteration 1): Use contains function and establish its relationship with sequence membership */
        let char_in_str2 = contains(str2, str1[i]);
        assert(char_in_str2 <==> str2@.contains(str1[i as int]));
        
        if !char_in_str2 {
            /* code modified by LLM (iteration 1): Establish preconditions before push */
            assert(!str2@.contains(str1[i as int]));
            assert(str1@.contains(str1[i as int]));
            
            result.push(str1[i]);
            
            /* code modified by LLM (iteration 1): Establish that the character is now in result after push */
            let result_len = result.len();
            assert(result[result_len - 1] == str1[i as int]);
            assert(result@.contains(str1[i as int]));
        }
        
        /* code modified by LLM (iteration 1): Assert the key property that maintains the second invariant */
        assert(forall|j: int| 0 <= j <= i ==> (str2@.contains(str1[j]) || result@.contains(str1[j])));
    }
    
    result
}

} // verus!