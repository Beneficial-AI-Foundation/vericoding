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
    let mut even_list: Vec<i32> = Vec::new();
    let mut i = 0;

    assert(even_list.len() == 0);

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|x: int| 0 <= x < even_list.len() ==> is_even(even_list[x] as int) && exists|j: int| 0 <= j < arr.len() && #[trigger] arr[j] == even_list[x],
            forall|x: int| 0 <= x < i && is_even(arr[x] as int) ==> exists|j: int| 0 <= j < even_list.len() && #[trigger] even_list[j] == arr[x],
    {
        let num = arr[i];
        if is_even(num as int) {
            even_list.push(num);
        }
        i = i + 1;
    }

    even_list
}
// </vc-code>

fn main() {
}

}