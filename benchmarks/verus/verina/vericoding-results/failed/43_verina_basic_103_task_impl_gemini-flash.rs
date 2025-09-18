// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clause to the `while` loop for termination proof. */
fn update_elements_helper(a: &Vec<i32>, index: usize, value: i32) -> (result: Vec<i32>)
    requires
        0 <= index < a.len(),
    ensures
        result.len() == a.len(),
        result@.len() == a@.len(),
        (index as int) < result.len(),
        result@[index as int] == value,
        forall|i: int| 0 <= i < a.len() && i != index as int ==> result@[i] == a@[i],
{
    let mut new_vec = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i as int <= a.len(),
            new_vec.len() == i,
            forall|j: int| 0 <= j < i as int ==> (j == index as int && #[trigger] new_vec@[j] == value) || (j != index as int && #[trigger] new_vec@[j] == a@[j]),
        decreases a.len() - i
    {

        if i == index {
            new_vec.push(value);
        } else {
            new_vec.push(*a.get(i).unwrap());
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
/* code modified by LLM (iteration 5): No logical changes; the helper function now compiles, so this should pass. */
{
    let mut result_vec = a.clone();

    result_vec = update_elements_helper(&result_vec, 4, a.get(4).unwrap() + 3);

    result_vec = update_elements_helper(&result_vec, 7, 516);

    result_vec
}
// </vc-code>

}
fn main() {}