use vstd::prelude::*;
fn main() {
    // Example usage
    let arr = vec![1, 3, 4, 7];
    let result = is_product_even(&arr);
    println!("Array contains even number: {}", result);
}

verus! {

spec fn is_even(n: u32) -> bool {
    (n % 2) == 0
}

fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    for i in 0..arr.len()
        invariant
            forall|k: int| 0 <= k < i ==> !is_even(arr[k])
    {
        if is_even(arr[i]) {
            return true;
        }
    }
    false
}

} // verus!