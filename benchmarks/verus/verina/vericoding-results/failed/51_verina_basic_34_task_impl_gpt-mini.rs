// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable even-check */
fn is_even_exec(n: i32) -> bool {
    n % 2 == 0
}

// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) ==> is_even(x) && arr@.contains(x),
        forall|x: i32| arr@.contains(x) && is_even(x) ==> result@.contains(x),
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i <= j && 
            is_even(arr[i]) && is_even(arr[j]) ==> {
                exists|ri: int, rj: int| 0 <= ri < result.len() && 0 <= rj < result.len() && 
                    ri <= rj && result[ri] == arr[i] && result[rj] == arr[j]
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use executable is_even_exec to check parity */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n: usize = arr.len();
    while i < n
        invariant
            forall|ri: int| 0 <= ri && ri < result@.len() ==> exists|ai: int| 0 <= ai && ai < i as int && result@[ri] == arr@[ai] && is_even(arr@[ai]),
            forall|ai: int| 0 <= ai && ai < i as int && is_even(arr@[ai]) ==> exists|ri: int| 0 <= ri && ri < result@.len() && result@[ri] == arr@[ai],
            forall|ai: int, aj: int| 0 <= ai && ai < i as int && 0 <= aj && aj < i as int && ai <= aj && is_even(arr@[ai]) && is_even(arr@[aj]) ==> {
                exists|ri: int, rj: int| 0 <= ri && ri < result@.len() && 0 <= rj && rj < result@.len() && ri <= rj && result@[ri] == arr@[ai] && result@[rj] == arr@[aj]
            },
        decreases (n as int) - (i as int)
    {
        let v = arr[i];
        if is_even_exec(v) {
            result.push(v);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}