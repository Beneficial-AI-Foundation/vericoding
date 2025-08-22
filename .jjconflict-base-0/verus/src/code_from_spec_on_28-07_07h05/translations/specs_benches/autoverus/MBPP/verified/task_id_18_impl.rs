use vstd::prelude::*;

fn main() {
    // Main function implementation not required for verification
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    // The lemma is proven by Verus automatically based on the semantics of push
}

fn contains(str: &[u8], key: u8) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut j = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while j < str.len()
        invariant
            forall|k: int| 0 <= k < j ==> str[k] != key,
        decreases str.len() - j,
    {
        if str[j] == key {
            return true;
        }
        j += 1;
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
    let mut i = 0;
    
    while i < str1.len()
        invariant
            i <= str1.len(),
            forall|k: int|
                0 <= k < result.len() ==> (str1@.contains(#[trigger] result[k]) && !str2@.contains(
                    #[trigger] result[k],
                )),
            forall|k: int|
                0 <= k < i ==> (str2@.contains(#[trigger] str1[k]) || result@.contains(
                    #[trigger] str1[k],
                )),
        decreases str1.len() - i,
    {
        let ch = str1[i];
        if !contains(str2, ch) {
            /* code modified by LLM (iteration 4): added ghost variable to capture old result state */
            let ghost old_result = result@;
            /* code modified by LLM (iteration 4): added assertion about str2 not containing ch */
            assert(!str2@.contains(ch));
            /* code modified by LLM (iteration 4): added assertion that ch is in str1 */
            assert(str1@.contains(ch));
            result.push(ch);
            /* code modified by LLM (iteration 4): added assertion using push semantics */
            assert(result@ == old_result.push(ch));
            /* code modified by LLM (iteration 4): added assertion that ch is now in result */
            assert(result@.contains(ch));
            /* code modified by LLM (iteration 4): added assertion to maintain invariant for existing elements */
            assert(forall|x: u8| old_result.contains(x) ==> result@.contains(x));
        } else {
            /* code modified by LLM (iteration 4): added assertion when ch is in str2 */
            assert(str2@.contains(ch));
        }
        i += 1;
        /* code modified by LLM (iteration 4): added assertion to help prove loop invariant maintenance */
        assert(forall|k: int| 0 <= k < i ==> (str2@.contains(str1[k]) || result@.contains(str1[k])));
    }
    
    result
}

} // verus!