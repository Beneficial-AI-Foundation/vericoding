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
        /* code modified by LLM (iteration 3): added decreases clause to fix verification error */
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

proof fn lemma_contains_equiv(vec: &Vec<char>, key: char)
    ensures
        /* code modified by LLM (iteration 2): fixed mode issue by calling spec mode contains */
        (exists|i: int| 0 <= i < vec.len() && (vec[i] == key)) <==> vec@.contains(key)
{
}

proof fn lemma_push_contains<T>(vec: Seq<T>, elem: T, x: T)
    ensures
        vec.push(elem).contains(x) <==> (vec.contains(x) || x == elem)
{
    /* code modified by LLM (iteration 5): complete proof for lemma_push_contains */
    if vec.contains(x) {
        let i = choose|i: int| 0 <= i < vec.len() && vec[i] == x;
        assert(vec.push(elem)[i] == x);
        assert(vec.push(elem).contains(x));
    }
    if x == elem {
        let last_idx = vec.len();
        assert(vec.push(elem)[last_idx] == elem);
        assert(vec.push(elem)[last_idx] == x);
        assert(vec.push(elem).contains(x));
    }
    if vec.push(elem).contains(x) {
        let i = choose|i: int| 0 <= i < vec.push(elem).len() && vec.push(elem)[i] == x;
        if i < vec.len() {
            assert(vec[i] == x);
            assert(vec.contains(x));
        } else {
            assert(i == vec.len());
            assert(vec.push(elem)[i] == elem);
            assert(x == elem);
        }
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    let mut result: Vec<char> = Vec::new();
    let mut i = 0;
    
    while i < str1.len()
        invariant
            0 <= i <= str1.len(),
            forall|j: int| 0 <= j < result.len() ==> (str1@.contains(#[trigger] result[j]) && !str2@.contains(#[trigger] result[j])),
            forall|j: int| 0 <= j < i ==> (str2@.contains(#[trigger] str1[j]) || result@.contains(#[trigger] str1[j])),
        /* code modified by LLM (iteration 3): added decreases clause to fix verification error */
        decreases str1.len() - i
    {
        let ch = str1[i];
        if !contains(str2, ch) {
            /* code modified by LLM (iteration 5): fixed proof structure and assertions */
            proof {
                lemma_contains_equiv(str2, ch);
                assert(!str2@.contains(ch));
                assert(str1@.contains(ch));
            }
            let old_result = result@;
            result.push(ch);
            proof {
                lemma_push_contains(old_result, ch, ch);
                assert(result@.contains(ch));
                assert(forall|k: int| 0 <= k < old_result.len() ==> old_result[k] == result@[k]);
                assert(forall|j: int| 0 <= j < old_result.len() ==> (str1@.contains(result@[j]) && !str2@.contains(result@[j])));
                assert(str1@.contains(result@[old_result.len()]));
                assert(!str2@.contains(result@[old_result.len()]));
                assert(forall|j: int| 0 <= j < i ==> (str2@.contains(str1[j]) || old_result.contains(str1[j])));
                assert(forall|j: int| 0 <= j < i ==> (str2@.contains(str1[j]) || result@.contains(str1[j])) by {
                    if 0 <= j < i {
                        if !str2@.contains(str1[j]) {
                            assert(old_result.contains(str1[j]));
                            lemma_push_contains(old_result, ch, str1[j]);
                            assert(result@.contains(str1[j]));
                        }
                    }
                });
                assert(str2@.contains(str1[i as int]) || result@.contains(str1[i as int]));
            }
        } else {
            proof {
                lemma_contains_equiv(str2, ch);
                assert(str2@.contains(ch));
                assert(str2@.contains(str1[i as int]));
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}