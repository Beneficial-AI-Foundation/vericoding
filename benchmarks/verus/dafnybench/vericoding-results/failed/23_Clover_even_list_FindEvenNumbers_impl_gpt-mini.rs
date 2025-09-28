use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_numbers: Vec<i32>)
    ensures 
        (forall|x: i32| arr@.contains(x) && x % 2 == 0 ==> even_numbers@.contains(x)) &&
        (forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x)) &&
        (forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0) &&
        (forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr@.len() && 
            #[trigger] even_numbers@[k] == #[trigger] arr@[n] && 
            #[trigger] even_numbers@[l] == #[trigger] arr@[m])
// </vc-spec>
// <vc-code>
{
    let mut even_numbers: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < arr@.len() {
        invariant { i <= arr@.len() }
        invariant { forall|k: nat| k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0 }
        invariant { forall|k: nat| k < even_numbers@.len() ==>
            exists|n: nat| n < i && even_numbers@[k] == arr@[n] }
        invariant { forall|k: nat, l: nat| k < l && l < even_numbers@.len() ==>
            exists|n: nat, m: nat| n < m && m < i && even_numbers@[k] == arr@[n] && even_numbers@[l] == arr@[m] }
        invariant { forall|n: nat| n < i && arr@[n] % 2 == 0 ==> even_numbers@.contains(arr@[n]) }
        decreases arr@.len() - i
    {
        let a: i32 = arr[i as usize];
        if a % 2 == 0 {
            even_numbers.push(a);
        }
        i = i + 1;
    }
    even_numbers
}
// </vc-code>

fn main() {
}

}