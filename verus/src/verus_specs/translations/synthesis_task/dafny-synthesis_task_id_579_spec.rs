use vstd::prelude::*;

verus! {

spec fn in_array(a: &[i32], x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i as int] == x
}

pub fn dissimilar_elements(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) ==> (in_array(a, x) != in_array(b, x)),
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] != result@[j],
{
}

}