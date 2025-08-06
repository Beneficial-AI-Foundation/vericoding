use vstd::prelude::*;

fn main() {
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    assert forall|k: int| 0 <= k < vec.len() implies #[trigger] vec[k] == vec.push(i)[k] by {
        assert(vec.push(i)[k] == vec[k]);
    }
    assert(vec.push(i).index(l as int) == i);
}

fn contains(str: &[u8], key: u8) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut j = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while j < str.len()
        invariant
            forall|i: int| 0 <= i < j ==> str[i] != key,
        decreases str.len() - j
    {
        if str[j] == key {
            return true;
        }
        j += 1;
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
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < str1.len()
        invariant
            forall|j: int|
                0 <= j < result.len() ==> (str1@.contains(#[trigger] result[j]) && !str2@.contains(
                    #[trigger] result[j],
                )),
            forall|j: int|
                0 <= j < i ==> (str2@.contains(#[trigger] str1[j]) || result@.contains(
                    #[trigger] str1[j],
                )),
        decreases str1.len() - i
    {
        let ch = str1[i];
        if !contains(str2, ch) {
            result.push(ch);
        }
        i += 1;
    }
    result
}

} // verus!