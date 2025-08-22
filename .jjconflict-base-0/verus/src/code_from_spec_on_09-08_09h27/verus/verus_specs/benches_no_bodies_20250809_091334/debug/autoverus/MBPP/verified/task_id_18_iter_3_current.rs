use vstd::prelude::*;

fn main() {
    let str1 = b"hello world";
    let str2 = b"lo";
    let result = remove_chars(str1, str2);
    println!("Result: {:?}", result);
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    // The lemma is about basic properties of sequence push operation
    // For any index k in the original sequence, the element remains the same
    assert forall|k: int| 0 <= k < vec.len() implies vec[k] == vec.push(i)[k] by {
        // This follows from the definition of push - it appends to the end
        assert(vec.push(i).len() == vec.len() + 1);
        /* code modified by LLM (iteration 1): cast vec.len() to int for subrange */
        assert(vec.push(i).subrange(0, vec.len() as int) == vec);
    };
    
    // The new element is at position l (which equals vec.len())
    assert(vec.push(i).len() == vec.len() + 1);
    assert(l as int == vec.len());
    assert(vec.push(i)[l as int] == i);
}

fn contains(str: &[u8], key: u8) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            forall|j: int| 0 <= j < i ==> str[j] != key,
        /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
        decreases str.len() - i,
    {
        if str[i] == key {
            return true;
        }
        i += 1;
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
        /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
        decreases str1.len() - i,
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