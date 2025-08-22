use vstd::prelude::*;

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    // pre-conditions-start
    requires
        l == vec.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
    // post-conditions-end
{
    // The properties follow directly from the definition of push
    // push appends an element to the end, so all original indices remain unchanged
    // and the new element is at position l (which equals vec.len())
}

fn contains(str: &Vec<char>, key: char) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    // post-conditions-end
{
    let mut idx = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < str.len()
        invariant
            forall|i: int| 0 <= i < idx ==> str[i] != key,
        decreases str.len() - idx
    {
        if str[idx] == key {
            return true;
        }
        idx += 1;
    }
    false
}

fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                #[trigger] str1[i],
            )),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < str1.len()
        invariant
            idx <= str1.len(),
            forall|i: int|
                0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                    #[trigger] result[i],
                )),
            forall|i: int|
                0 <= i < idx ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                    #[trigger] str1[i],
                )),
        decreases str1.len() - idx
    {
        let ch = str1[idx];
        if !contains(str2, ch) {
            result.push(ch);
        }
        idx += 1;
    }
    
    result
}

} // verus!

fn main() {}