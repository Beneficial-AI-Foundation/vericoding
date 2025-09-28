// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed push method calls to handle Seq types correctly */
spec fn update_element_at_index(a: Seq<i32>, index: int, value: i32) -> Seq<i32>
    requires 0 <= index < a.len(),
    ensures
        update_element_at_index(a, index, value).len() == a.len(),
        forall|i: int| 0 <= i < a.len() && i != index ==> #[trigger] update_element_at_index(a, index, value)[i] == a[i],
        update_element_at_index(a, index, value)[index] == value,
    decreases index,
{
    if index == 0 {
        seq![value] + a.skip(1)
    } else {
        seq![a[0]] + update_element_at_index(a.skip(1), index - 1, value)
    }
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
/* code modified by LLM (iteration 5): simplified implementation to directly update elements */
{
    let mut result = a.clone();
    result[4] = a[4] + 3;
    result[7] = 516;
    result
}
// </vc-code>

}
fn main() {}