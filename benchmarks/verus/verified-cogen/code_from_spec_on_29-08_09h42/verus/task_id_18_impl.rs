use vstd::prelude::*;


verus! {

// <vc-helpers>
fn contains(str: &Vec<char>, key: char) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    // post-conditions-end
{
    // impl-start
    let mut i = 0;
    while i < str.len()
        // invariants-start
        invariant
            forall|m: int| 0 <= m < i ==> (str[m] != key),
        // invariants-end
        /* code modified by LLM (iteration 2): added decreases clause */
        decreases str.len() - i
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
    // impl-end
}

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
    // impl-end
}

proof fn lemma_result_char_in_str1(str1: &Vec<char>, str2: &Vec<char>, result: &Vec<char>, ch: char, i: int)
    requires
        0 <= i < result.len(),
        result[i] == ch,
        forall|j: int| 0 <= j < result.len() ==> (str1@.contains(result[j]) && !str2@.contains(result[j])),
    ensures
        str1@.contains(ch) && !str2@.contains(ch),
{
}

proof fn lemma_str1_char_handled(str1: &Vec<char>, str2: &Vec<char>, result: &Vec<char>, ch: char, i: int)
    requires
        0 <= i < str1.len(),
        str1[i] == ch,
        forall|j: int| 0 <= j < str1.len() ==> (str2@.contains(str1[j]) || result@.contains(str1[j])),
    ensures
        str2@.contains(ch) || result@.contains(ch),
{
}
// pure-end
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|j: int| 0 <= j < result.len() ==> (str1@.contains(result[j]) && !str2@.contains(result[j])),
            forall|j: int| 0 <= j < i ==> (str2@.contains(str1[j]) || result@.contains(str1[j])),
        /* code modified by LLM (iteration 2): added decreases clause */
        decreases str1.len() - i
    {
        let ch = str1[i];
        if !contains(str2, ch) {
            /* code modified by LLM (iteration 3): moved proof block before push and added assertion for new invariant */
            proof {
                let old_result = result@;
                lemma_vec_push(old_result, ch, result.len());
                assert(str1@.contains(ch));
                assert(!str2@.contains(ch));
            }
            result.push(ch);
        }
        i += 1;
    }
    
    result
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}