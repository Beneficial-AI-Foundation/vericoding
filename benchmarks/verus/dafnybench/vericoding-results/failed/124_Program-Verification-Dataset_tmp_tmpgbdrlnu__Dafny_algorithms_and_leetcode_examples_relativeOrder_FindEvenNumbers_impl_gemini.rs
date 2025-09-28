// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[int]) -> (even_numbers: Vec<int>)
    ensures

        forall|i: int| 0 <= i < arr.len() && is_even(arr[i]) ==> 
            #[trigger] even_numbers@.contains(arr[i]),

        forall|x: int| #[trigger] even_numbers@.contains(x) ==> 
            exists|i: int| 0 <= i < arr.len() && arr[i] == x,

        forall|k: int, l: int| 0 <= k < l < even_numbers.len() ==>
            exists|n: int, m: int| 0 <= n < m < arr.len() && 
                #[trigger] even_numbers[k] == arr[n] && 
                #[trigger] even_numbers[l] == arr[m]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected types in invariants and exec code based on error messages. */
    let mut even_numbers: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: nat| (j as usize) < i && is_even(arr@[j as int]) ==> 
                even_numbers@.map(|e: i32| e as int).contains(arr@[j as int]),
            forall|x: i32| #[trigger] even_numbers@.contains(x) ==> 
                is_even(x as int) && (exists|j: nat| (j as usize) < i && arr@[j as int] == x as int),
            forall|k: nat, l: nat| k < l < even_numbers@.len() ==> 
                exists|n: nat, m: nat| n < m < (i as nat) && 
                    (even_numbers@[k as int] as int) == arr@[n as int] && 
                    (even_numbers@[l as int] as int) == arr@[m as int],
        decreases arr.len() - i
    {
        let current_element = arr[i];
        if current_element % 2int == 0int {
            proof {
                assert(even_numbers@.map(|e: i32| e as int).push(current_element).contains(current_element));
            }
            even_numbers.push(current_element as i32);
        }
        i = i + 1;
    }
    even_numbers
}
// </vc-code>

}
fn main() {}