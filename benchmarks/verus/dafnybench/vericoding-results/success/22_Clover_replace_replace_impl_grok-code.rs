use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace(arr: &mut Vec<i32>, k: i32)
    ensures 
        forall|i: int| 0 <= i < old(arr).len() ==> old(arr)[i] > k ==> arr[i] == -1,
        forall|i: int| 0 <= i < old(arr).len() ==> old(arr)[i] <= k ==> arr[i] == old(arr)[i],
// </vc-spec>
// <vc-code>
{
    let ghost old_seq: Seq<i32> = (*arr).deep_view();
    let mut i: usize = 0;
    while i < arr.len()
        invariant 
            0 <= i as int <= arr.view().len() as int,
            forall |j: int| #![trigger(arr.view()[j])] 0 <= j < i as int ==> 
                (old_seq[j] > k ==> arr.view()[j] == (-1i32)) && 
                (old_seq[j] <= k ==> arr.view()[j] == old_seq[j]),
            forall |j: int| #![trigger(arr.view()[j])] i as int <= j < old_seq.len() as int ==> arr.view()[j] == old_seq[j],
            arr.view().len() == old_seq.len(),
        decreases arr.len() as int - i as int
    {
        proof {
            assert(arr.view()[i as int] == old_seq[i as int]);
        }
        if arr[i] > k {
            arr[i] = -1i32;
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}

}