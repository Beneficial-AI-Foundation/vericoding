// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed `let res: &Vec<i32> = &result;` from the ensures clause of `create_new_vec_with_updates` as trigger cannot contain variables. */
fn create_new_vec_with_updates(a: &Vec<i32>, index1: usize, value1: i32, index2: usize, value2: i32) -> (result: Vec<i32>)
    requires
        a.len() > index1,
        a.len() > index2,
    ensures
        result.len() == a.len(),
        ({let res: &Vec<i32> = &result; res@.index(index1 as int) == value1}),
        ({let res: &Vec<i32> = &result; res@.index(index2 as int) == value2}),
        forall|i: int| 0 <= i < a.len() as int && i != index1 as int && i != index2 as int ==> #[trigger]result@.index(i) == a@.index(i),
{
    let mut new_vec = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            new_vec.len() == i,
            forall|j: int| 0 <= j < i as int && j != index1 as int && j != index2 as int ==> #[trigger]new_vec@.index(j) == a@.index(j),
            (i > index1) ==> new_vec@.index(index1 as int) == value1,
            (i > index2) ==> new_vec@.index(index2 as int) == value2,
        decreases a.len() - i
    {
        if i == index1 {
            new_vec.push(value1);
        } else if i == index2 {
            new_vec.push(value2);
        } else {
            new_vec.push(a[i]);
        }
        i = i + 1;
    }
    new_vec
}
// </vc-helpers>

// <vc-spec>
fn update_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() >= 8,
    ensures
        result[4] == a[4] + 3,
        result[7] == 516,
        forall|i: int| 0 <= i < a.len() && i != 4 && i != 7 ==> result[i] == a[i],
        result.len() == a.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Used `create_new_vec_with_updates` to generate the new vector based on the specified updates. */
{
    let result = create_new_vec_with_updates(a, 4, a[4] + 3, 7, 516);
    result
}
// </vc-code>

}
fn main() {}