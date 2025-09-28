// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added axiomatic lemma for push preserving index */
proof fn lemma_push_preserves_index<T>(s: Seq<T>, t: T, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.push(t)@[i] == s@[i],
{
}

/* helper modified by LLM (iteration 4): added lemma to prove push preserves contains */
proof fn lemma_push_preserves_contains<T>(s: Seq<T>, t: T, v: T)
    requires
        s.contains(v),
    ensures
        s.push(t).contains(v),
{
    let j = choose|j: int| 0 <= j < s.len() && s@[j] == v;
    lemma_push_preserves_index(s, t, j);
    assert(s.push(t)@[j] == v);
}
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_list: Vec<i32>)

    ensures 
        forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == even_list[i],

        forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> exists|j: int| 0 <= j < even_list.len() && even_list[j] == arr[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): re-submitting logic from previous turn with fixed helpers */
    let mut even_list: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= (i as int) <= arr@.len(),
            forall|k: int| 0 <= k < even_list@.len() ==> 
                is_even(even_list@[k] as int) &&
                (exists|j: int| 0 <= j < (i as int) && arr@[j] == even_list@[k]),
            forall|k: int| 0 <= k < (i as int) && is_even(arr@[k] as int) ==> 
                even_list@.contains(arr@[k]),
        decreases arr@.len() - (i as int)
    {
        let element = arr[i];
        if element % 2 == 0 {
            let ghost old_spec = even_list@;
            even_list.push(element);
            assert forall|k: int| 0 <= k < (i as int) && is_even(arr@[k] as int) implies
                even_list@.contains(arr@[k])
            by {
                let val_k = arr@[k];
                assert(old_spec.contains(val_k));
                lemma_push_preserves_contains(old_spec, element, val_k);
                assert(even_list@.contains(val_k));
            }
        }
        i = i + 1;
    }
    even_list
}
// </vc-code>

}
fn main() {}