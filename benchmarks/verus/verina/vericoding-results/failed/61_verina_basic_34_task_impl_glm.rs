// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: i32) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed function to take int and added type conversions */
exec fn is_even_exec(n: i32) -> bool {
    n % 2 == 0
}

proof fn is_even_exec_equiv(n: int)
    ensures is_even_exec(n as i32) == is_even(n as i32)
{
    assert(is_even_exec(n as i32) == (n as i32 % 2 == 0));
    assert(is_even(n as i32) == (n as i32 % 2 == 0));
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
/* code modified by LLM (iteration 5): fixed type conversion in proof call */
{
    let mut result = Vec::new();
    for i in 0..arr.len()
        invariant
            result.len() <= i,
            forall|k: int| 0 <= k < i ==> 
                (is_even(arr[k]) ==> {
                    exists|rk: int| 0 <= rk < result.len() && result[rk] == arr[k]
                }),
            forall|k1: int, k2: int| 0 <= k1 < k2 < i && is_even(arr[k1]) && is_even(arr[k2]) ==> {
                exists|rk1: int, rk2: int| 0 <= rk1 < result.len() && 0 <= rk2 < result.len() && 
                    rk1 < rk2 && 
                    result[rk1] == arr[k1] && result[rk2] == arr[k2]
            }
    {
        if is_even_exec(arr[i]) {
            proof {
                is_even_exec_equiv(arr[i] as int);
            }
            result.push(arr[i]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}