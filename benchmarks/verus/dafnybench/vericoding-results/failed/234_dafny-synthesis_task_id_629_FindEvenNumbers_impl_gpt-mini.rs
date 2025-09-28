use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

// <vc-helpers>
proof fn helper_noop() {
}
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
    let mut i: nat = 0;
    while i < arr.len()
        invariant i <= arr.len()
        invariant forall|t: nat| t < even_list.len() ==>
            is_even(even_list@[t] as int) && exists|j: nat| j < i && arr@[j] == even_list@[t]
        invariant forall|j: nat| j < i && is_even(arr@[j] as int) ==>
            exists|t: nat| t < even_list.len() && even_list@[t] == arr@[j]
    {
        let v = arr[i];
        if is_even(v as int) {
            let old_len = even_list.len();
            even_list.push(v);
            proof {
                // length increased by one
                assert(old_len + 1 == even_list.len());

                // new element equals arr[i] and is even
                assert(even_list@[old_len] == v);
                assert(is_even(v as int));
                assert(arr@[i] == v);

                // witness for the new element with j = i (shows existence with bound i+1)
                assert(exists|j: nat| j == i && j < i + 1 && arr@[j] == even_list@[old_len]);

                // existing elements (t < old_len) satisfied the old invariant:
                assert(forall|t: nat| t < old_len ==>
                    is_even(even_list@[t] as int) && exists|j: nat| j < i && arr@[j] == even_list@[t]
                );
                // from j < i we get j < i+1, so upgrade the witness bound to i+1
                assert(forall|t: nat| t < old_len ==>
                    is_even(even_list@[t] as int) && exists|j: nat| j < i + 1 && arr@[j] == even_list@[t]
                );

                // combine to obtain the invariant for all t < even_list.len() with bound i+1
                assert(forall|t: nat| t < even_list.len() ==>
                    is_even(even_list@[t] as int) && exists|j: nat| j < i + 1 && arr@[j] == even_list@[t]
                );
            }
        }
        i += 1;
    }
    even_list
}
// </vc-code>

fn main() {
}

}