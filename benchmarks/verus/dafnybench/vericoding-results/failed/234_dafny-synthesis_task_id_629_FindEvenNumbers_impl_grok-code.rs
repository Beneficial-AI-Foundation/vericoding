use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
// No additional helpers needed.
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_list: Vec<i32>)
    // All numbers in the output are even and exist in the input 
    ensures forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == even_list[i],
    // All even numbers in the input are in the output
    ensures forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> exists|j: int| 0 <= j < even_list.len() && even_list[j] == arr[i]
// </vc-spec>
// <vc-code>
{
let mut result = Vec::new();
let mut i = 0;
while i < arr.len()
    invariant
        0 <= i <= arr.len(),
        forall|[k: int]| #[trigger] 0 <= k < result.len() ==> 
            is_even(result@[k] as int) && exists|[j: int]| #[trigger] 0 <= j <= i && arr@[j] == result@[k],
        forall|[j: int]| #[trigger] 0 <= j <= i && is_even(arr@[j] as int) ==>
            exists|[k: int]| #[trigger] 0 <= k < result.len() && result@[k] == arr@[j],
{
    if is_even(arr[i] as int) {
        result.push(arr[i]);
        proof {
            assert(result@[result.len() - 1] == arr@[i]);
        }
    }
    i += 1;
}
result
}
// </vc-code>

fn main() {
}

}