use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_position_exists(arr: &[i32], even_numbers: &Vec<i32>, k: int)
    requires 
        0 <= k < even_numbers.len(),
        forall|i: int| 0 <= i < even_numbers.len() ==> even_numbers@[i] % 2 == 0,
        forall|i: int| 0 <= i < even_numbers.len() ==> arr@.contains(even_numbers@[i]),
        forall|i: int, j: int| 0 <= i < j < even_numbers.len() ==> {
            let val_i = even_numbers@[i];
            let val_j = even_numbers@[j];
            let pos_i = choose|p: int| 0 <= p < arr.len() && arr@[p] == val_i;
            let pos_j = choose|p: int| 0 <= p < arr.len() && arr@[p] == val_j;
            pos_i < pos_j
        }
    ensures exists|n: int| 0 <= n < arr.len() && arr@[n] == even_numbers@[k]
{
}

proof fn lemma_order_maintained(arr: &[i32], even_numbers: &Vec<i32>, k: int, l: int)
    requires 
        0 <= k < l < even_numbers.len(),
        forall|i: int| 0 <= i < even_numbers.len() ==> even_numbers@[i] % 2 == 0,
        forall|i: int| 0 <= i < even_numbers.len() ==> arr@.contains(even_numbers@[i]),
        forall|i: int, j: int| 0 <= i < j < even_numbers.len() ==> {
            let val_i = even_numbers@[i];
            let val_j = even_numbers@[j];
            let pos_i = choose|p: int| 0 <= p < arr.len() && arr@[p] == val_i;
            let pos_j = choose|p: int| 0 <= p < arr.len() && arr@[p] == val_j;
            pos_i < pos_j
        }
    ensures exists|n: int, m: int| 0 <= n < m < arr.len() && 
            even_numbers@[k] == arr@[n] && 
            even_numbers@[l] == arr@[m]
{
    let val_k = even_numbers@[k];
    let val_l = even_numbers@[l];
    let pos_k = choose|p: int| 0 <= p < arr.len() && arr@[p] == val_k;
    let pos_l = choose|p: int| 0 <= p < arr.len() && arr@[p] == val_l;
}
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
    let mut even_numbers = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|x: i32| arr@.subrange(0, i as int).contains(x) && x % 2 == 0 ==> even_numbers@.contains(x),
            forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x),
            forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0,
            forall|k: int| 0 <= k < even_numbers@.len() ==> arr@.contains(even_numbers@[k]),
            forall|j: int, k: int| 0 <= j < k < even_numbers@.len() ==> {
                let val_j = even_numbers@[j];
                let val_k = even_numbers@[k];
                let pos_j = choose|p: int| 0 <= p < arr.len() && arr@[p] == val_j;
                let pos_k = choose|p: int| 0 <= p < arr.len() && arr@[p] == val_k;
                pos_j < pos_k
            }
        decreases arr.len() - i
    {
        if arr[i] % 2 == 0 {
            even_numbers.push(arr[i]);
        }
        i += 1;
    }
    
    assert(arr@.subrange(0, arr.len() as int) =~= arr@);
    
    even_numbers
}
// </vc-code>

fn main() {
}

}