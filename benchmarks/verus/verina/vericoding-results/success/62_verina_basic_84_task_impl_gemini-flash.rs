// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added spec fn and moved replace_element into the code */
spec fn replace_element_spec(element: int, k: int) -> int {
    if element > k {
        -1
    } else {
        element
    }
}
// </vc-helpers>

// <vc-spec>
fn replace(arr: &Vec<i32>, k: i32) -> (result: Vec<i32>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] > k ==> result[i] == -1),
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] <= k ==> result[i] == arr[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added decreases clause to while loop and used replace_element_spec in invariant */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i && i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (arr[j] > k ==> result[j] == -1),
            forall|j: int| 0 <= j < i ==> (arr[j] <= k ==> result[j] == arr[j]),
            forall|j: int| 0 <= j < i ==> result[j] == replace_element_spec(arr[j] as int, k as int),
        decreases arr.len() as int - i as int
    {
        let element = arr[i];
        let new_element = if element > k { -1 } else { element };
        result.push(new_element);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}