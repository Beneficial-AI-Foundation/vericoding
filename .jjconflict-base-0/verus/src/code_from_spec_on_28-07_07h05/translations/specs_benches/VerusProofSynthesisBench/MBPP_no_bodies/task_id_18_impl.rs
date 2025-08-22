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
    // The proof is automatic - Verus can prove these properties about sequence push
    // impl-end
}

fn contains(str: &Vec<char>, key: char) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    // post-conditions-end
{
    let mut j = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while j < str.len()
        invariant
            0 <= j <= str.len(),
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
            forall|k: int|
                0 <= k < i ==> (str2@.contains(#[trigger] str1[k]) || result@.contains(
                    #[trigger] str1[k],
                )),
        decreases str1.len() - i,
    {
        if !contains(str2, str1[i]) {
            /* code modified by LLM (iteration 3): fixed proof to properly establish invariant maintenance */
            proof {
                assert(!str2@.contains(str1[i as int]));
                assert(str1@.contains(str1[i as int]));
            }
            result.push(str1[i]);
            /* code modified by LLM (iteration 4): fixed syntax error by adding missing opening brace for 'by' clause */
            proof {
                let new_len = result@.len();
                assert(result@[new_len - 1] == str1[i as int]);
                assert(str1@.contains(result@[new_len - 1]));
                assert(!str2@.contains(result@[new_len - 1]));
                
                // Show that the second invariant is maintained for the new index i
                assert(result@.contains(str1[i as int]));
                
                // Show that for all previous indices, the invariant still holds
                assert(forall|k: int| 0 <= k < i ==> (str2@.contains(str1[k]) || result@.contains(str1[k])) by {
                    let old_result = old(result)@;
                    assert(forall|k: int| 0 <= k < i ==> (str2@.contains(str1[k]) || old_result.contains(str1[k])));
                    assert(forall|x: char| old_result.contains(x) ==> result@.contains(x));
                });
            }
        }
        i += 1;
    }
    result
}

} // verus!

fn main() {}