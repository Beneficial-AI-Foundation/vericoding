use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>

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
    for i in 0..arr.len()
        invariant 
            forall|j: int| 0 <= j < result.len() ==> is_even(result@[j] as int) && exists|k: int| 0 <= k < arr.len() && arr@[k] == result@[j],
            forall|k: int| 0 <= k < i ==> is_even(arr@[k] as int) ==> exists|j: int| 0 <= j < result.len() && result@[j] == arr@[k]
    {
        if is_even(arr[i] as int) {
            result.push(arr[i]);
            assert(forall|k: int| 0 <= k <= i ==> is_even(arr@[k] as int) ==> exists|j: int| 0 <= j < result.len() && result@[j] == arr@[k]) by {
                reveal(is_even);
                forall|k: int| 0 <= k <= i ensures is_even(arr@[k] as int) ==> exists|j: int| 0 <= j < result.len() && result@[j] == arr@[k] {
                    if k == i {
                        assert(arr@[i] == result@[result.len() - 1]);
                        assert(result@[result.len() - 1] == arr@[k]);
                        assert(exists|j| 0 <= j < result.len() && result@[j] == arr@[k] by {
                            reveal(is_even);
                        });
                    } else {
                        assert(k < i);
                        assert(exists|j: int| 0 <= j < (result.len() - 1) && result@[j] == arr@[k] by {
                            reveal(is_even);
                        });
                    }
                }
            }
        }
    }
    result
}
// </vc-code>

fn main() {
}

}