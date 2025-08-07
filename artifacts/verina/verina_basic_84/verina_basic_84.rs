use vstd::prelude::*;

verus! {

spec fn replace_precond(arr: Seq<i32>, k: i32) -> bool {
    true
}

fn replace_loop(old_arr: &Vec<i32>, k: i32, i: usize, acc: &mut Vec<i32>)
    requires 
        old_arr.len() == old(acc).len(),
        i <= old_arr.len(),
        // Elements before i have been processed correctly
        forall|j: int| 0 <= j < i ==> {
            if old_arr[j] > k {
                old(acc)[j] == -1
            } else {
                old(acc)[j] == old_arr[j]
            }
        },
        // Elements at i and after are unchanged from original
        forall|j: int| i <= j < old_arr.len() ==> old(acc)[j] == old_arr[j],
    ensures
        acc.len() == old_arr.len(),
        forall|j: int| 0 <= j < old_arr.len() ==> {
            if old_arr[j] > k {
                acc[j] == -1
            } else {
                acc[j] == old_arr[j]
            }
        },
    decreases old_arr.len() - i,
{
    if i < old_arr.len() {
        if old_arr[i] > k {
            acc.set(i, -1);
            replace_loop(old_arr, k, i + 1, acc);
        } else {
            replace_loop(old_arr, k, i + 1, acc);
        }
    }
}

fn replace(arr: &Vec<i32>, k: i32) -> (result: Vec<i32>)
    requires replace_precond(arr@, k),
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> {
            if arr[i] > k {
                result[i] == -1
            } else {
                result[i] == arr[i]
            }
        },
{
    let mut acc = arr.clone();
    replace_loop(arr, k, 0, &mut acc);
    acc
}

spec fn replace_postcond(arr: Seq<i32>, k: i32, result: Seq<i32>) -> bool {
    (forall|i: int| #![auto] 0 <= i < arr.len() ==> (arr[i] > k ==> result[i] == -1)) &&
    (forall|i: int| 0 <= i < arr.len() ==> (arr[i] <= k ==> result[i] == arr[i]))
}

// Theorem showing that the postcondition is equivalent to the ensures clause
proof fn replace_satisfies_postcond_lemma(arr: Vec<i32>, k: i32, result: Vec<i32>)
    requires 
        replace_precond(arr@, k),
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() as int ==> {
            if arr[i] > k {
                result[i] == -1
            } else {
                result[i] == arr[i]
            }
        },
    ensures replace_postcond(arr@, k, result@)
{
    // The postcondition follows directly from the preconditions
    // We just need to show the logical equivalence
}

} // verus!

fn main() {}