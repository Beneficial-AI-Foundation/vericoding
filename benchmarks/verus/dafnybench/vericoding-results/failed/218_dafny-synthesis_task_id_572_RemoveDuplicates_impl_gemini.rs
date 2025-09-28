// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed vec_contains invariant from .contains to forall */
fn vec_contains(haystack: &Vec<i32>, needle: i32) -> (b: bool)
    ensures b == haystack@.contains(needle)
{
    let mut i: usize = 0;
    while i < haystack.len()
        invariant
            i <= haystack.len(),
            forall|k: int| 0 <= k < (i as int) ==> haystack@[k] != needle,
        decreases haystack.len() - i
    {
        if haystack[i] == needle {
            return true;
        }
        i = i + 1;
    }
    return false;
}

proof fn lemma_preserves_uniqueness(s: Seq<i32>, x: i32)
    requires
        (forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]),
        !s.contains(x),
    ensures
        forall|i: int, j: int| 0 <= i < j < s.push(x).len() ==> s.push(x)[i] != s.push(x)[j],
{
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): added proof block to instantiate loop invariant */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result@[k] != result@[l],
            forall|x: i32| result@.contains(x) <==> (exists|j: int| 0 <= j < i as int && a[j] == x),
        decreases a.len() - i
    {
        let element = a[i];
        let is_present = vec_contains(&result, element);

        proof {
            assert(result@.contains(element) <==> (exists|j: int| 0 <= j < i as int && a[j] == element));
        }

        if !is_present {
            proof {
                lemma_preserves_uniqueness(result@, element);
            }
            result.push(element);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}