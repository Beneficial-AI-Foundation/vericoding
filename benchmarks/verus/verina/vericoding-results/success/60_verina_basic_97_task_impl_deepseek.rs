// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn set_index_preserves_other_elements<T>(s: Seq<T>, i: int, val: T)
    requires 0 <= i < s.len()
    ensures forall|k: int| 0 <= k < s.len() && k != i ==> s.update(i, val)[k] == s[k]
{
}

proof fn set_index_updates_correct_element<T>(s: Seq<T>, i: int, val: T)
    requires 0 <= i < s.len()
    ensures s.update(i, val)[i] == val
{
}

proof fn update_preserves_length<T>(s: Seq<T>, i: int, val: T)
    requires 0 <= i < s.len()
    ensures s.update(i, val).len() == s.len()
{
}

// </vc-helpers>

// <vc-spec>
fn test_array_elements(a: &Vec<i32>, j: usize) -> (result: Vec<i32>)
    requires j < a.len(),
    ensures
        result.len() == a.len(),
        result[j as int] == 60,
        forall|k: int| 0 <= k < a.len() && k != j ==> result[k] == a[k],
// </vc-spec>
// <vc-code>
{
    let mut result = a.clone();
    result.set(j, 60);
    result
}
// </vc-code>

}
fn main() {}