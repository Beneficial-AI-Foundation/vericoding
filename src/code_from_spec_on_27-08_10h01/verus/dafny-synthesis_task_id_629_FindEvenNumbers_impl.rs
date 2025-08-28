use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
proof fn lemma_even_preserved(n: i32)
    requires is_even(n as int)
    ensures is_even(n as int)
{
}

proof fn lemma_modulo_even(n: i32)
    requires n % 2 == 0
    ensures is_even(n as int)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_list: Vec<i32>)
    // All numbers in the output are even and exist in the input 
    ensures forall|i: int| 0 <= i < even_list.len() ==> is_even(even_list[i] as int) && exists|j: int| 0 <= j < arr.len() && arr[j] == even_list[i],
    // All even numbers in the input are in the output
    ensures forall|i: int| 0 <= i < arr.len() && is_even(arr[i] as int) ==> exists|j: int| 0 <= j < even_list.len() && even_list[j] == arr[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut even_list = Vec::new();
    
    let mut i = 0;
    while i < arr.len()
        invariant 0 <= i <= arr.len(),
        invariant forall|k: int| 0 <= k < even_list.len() ==> is_even(even_list[k] as int),
        invariant forall|k: int| 0 <= k < even_list.len() ==> exists|j: int| 0 <= j < arr.len() && arr[j] == even_list[k],
        invariant forall|k: int| 0 <= k < i && is_even(arr[k] as int) ==> exists|j: int| 0 <= j < even_list.len() && even_list[j] == arr[k]
    {
        if arr[i] % 2 == 0 {
            proof {
                lemma_modulo_even(arr[i]);
            }
            even_list.push(arr[i]);
        }
        i += 1;
    }
    
    even_list
}
// </vc-code>

fn main() {
}

}