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
    // impl-start
    // This is a proof lemma about the properties of push operation
    // The first postcondition states that all original elements remain at same indices
    // The second postcondition states that the new element is at index l
    // These properties follow directly from the definition of push
    // impl-end
}

fn contains(str: &Vec<char>, key: char) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    // post-conditions-end
{
    let mut j = 0;
    while j < str.len()
        invariant
            0 <= j <= str.len(),
            forall|k: int| 0 <= k < j ==> str[k] != key,
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases str.len() - j
    {
        if str[j] == key {
            return true;
        }
        j += 1;
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
    let mut i = 0;
    
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|j: int|
                0 <= j < result.len() ==> (str1@.contains(#[trigger] result[j]) && !str2@.contains(
                    #[trigger] result[j],
                )),
            forall|j: int|
                0 <= j < i ==> (str2@.contains(#[trigger] str1[j]) || result@.contains(
                    #[trigger] str1[j],
                )),
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases str1.len() - i
    {
        /* code modified by LLM (iteration 2): store the contains result and use assertion to connect boolean result with specification */
        let char_in_str2 = contains(str2, str1[i]);
        
        if !char_in_str2 {
            /* code modified by LLM (iteration 4): assert properties before and after push operation */
            assert(!str2@.contains(str1[i as int]));
            assert(str1@.contains(str1[i as int]));
            
            /* code modified by LLM (iteration 4): store old result for proof */
            let old_result = result@;
            result.push(str1[i]);
            
            /* code modified by LLM (iteration 4): prove that the pushed character satisfies the invariant */
            assert(str1@.contains(str1[i as int]) && !str2@.contains(str1[i as int]));
            assert(result@.contains(str1[i as int]));
            
            /* code modified by LLM (iteration 4): prove that all old elements still satisfy the invariant */
            assert(forall|j: int| 0 <= j < old_result.len() ==> old_result[j] == result@[j]);
        } else {
            /* code modified by LLM (iteration 3): cast i to int for sequence operations */
            assert(str2@.contains(str1[i as int]));
        }
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}