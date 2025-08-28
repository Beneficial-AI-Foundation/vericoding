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

proof fn lemma_contains_equiv(str: &Vec<char>, key: char)
    ensures
        str@.contains(key) <==> (exists|i: int| 0 <= i < str.len() && str[i] == key)
{
}

proof fn lemma_contains_push(vec: Seq<char>, ch: char, old_ch: char)
    ensures
        vec.contains(old_ch) ==> vec.push(ch).contains(old_ch)
{
    if vec.contains(old_ch) {
        let witness = choose|i: int| 0 <= i < vec.len() && vec[i] == old_ch;
        assert(0 <= witness < vec.push(ch).len());
        assert(vec.push(ch)[witness] == old_ch);
    }
}

proof fn lemma_push_preserves_contains(old_vec: Seq<char>, new_ch: char)
    ensures
        forall|old_ch: char| old_vec.contains(old_ch) ==> old_vec.push(new_ch).contains(old_ch)
{
    assert forall|old_ch: char| old_vec.contains(old_ch) implies old_vec.push(new_ch).contains(old_ch) by {
        lemma_contains_push(old_vec, new_ch, old_ch);
    }
}
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
            forall|j: int| 0 <= j < result.len() ==> 
                (str1@.contains(#[trigger] result[j]) && !str2@.contains(#[trigger] result[j])),
            forall|j: int| 0 <= j < i ==> 
                (str2@.contains(#[trigger] str1[j]) || result@.contains(#[trigger] str1[j])),
        decreases str1.len() - i
    {
        let ch = str1[i];
        if !contains(str2, ch) {
            proof {
                lemma_contains_equiv(str2, ch);
                lemma_contains_equiv(str1, ch);
            }
            result.push(ch);
            proof {
                lemma_push_preserves_contains(result@.drop_last(), ch);
                assert(result@.drop_last().push(ch) == result@);
                assert(result@.contains(ch));
                assert(forall|j: int| 0 <= j < i ==> 
                    (str2@.contains(str1[j]) || result@.drop_last().contains(str1[j]))) by {
                    assert(forall|j: int| 0 <= j < i ==> 
                        (str2@.contains(str1[j]) || result@.drop_last().contains(str1[j])));
                };
                assert(forall|j: int| 0 <= j < i ==> 
                    (str2@.contains(str1[j]) || result@.contains(str1[j]))) by {
                    assert forall|j: int| 0 <= j < i implies 
                        (str2@.contains(str1[j]) || result@.contains(str1[j])) by {
                        if !str2@.contains(str1[j]) {
                            assert(result@.drop_last().contains(str1[j]));
                            lemma_contains_push(result@.drop_last(), ch, str1[j]);
                            assert(result@.contains(str1[j]));
                        }
                    }
                };
                assert(!str2@.contains(ch));
                assert(result@.contains(ch));
                assert(str2@.contains(str1[i as int]) || result@.contains(str1[i as int]));
            }
        } else {
            proof {
                lemma_contains_equiv(str2, ch);
                assert(str2@.contains(str1[i as int]));
            }
        }
        i += 1;
    }
    
    result
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}