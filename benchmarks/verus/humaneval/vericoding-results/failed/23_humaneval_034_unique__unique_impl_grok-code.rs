// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i8>) -> (result: Vec<i8>)
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> (result@[i] as int) < (result@[j] as int) &&
        forall|x: i8| result@.contains(x) ==> s@.contains(x) &&
        forall|x: i8| s@.contains(x) ==> result@.contains(x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ref pattern issue by removing & before existing and dereferencing in comparison */
    let mut unique_list: Vec<i8> = Vec::new();
    for e in s {
        let mut is_new = true;
        for existing in &unique_list {
            if *existing == e {
                is_new = false;
                break;
            }
        }
        if is_new {
            unique_list.push(e);
        }
    }
    let n = unique_list.len();
    for i in 0..n {
        let mut min_index = i;
        for j in i+1..n {
            if unique_list[j] < unique_list[min_index] {
                min_index = j;
            }
        }
        let temp = unique_list[i];
        unique_list[i] = unique_list[min_index];
        unique_list[min_index] = temp;
    }
    unique_list
}
// </vc-code>


}

fn main() {}