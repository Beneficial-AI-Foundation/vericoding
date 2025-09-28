// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn rotate_right(arr: Seq<int>, k: int) -> Seq<int>
    recommends 0 <= k <= arr.len()
{
    if arr.len() == 0 {
        arr
    } else if k == 0 {
        arr
    } else {
        arr.subrange((arr.len() - k) as int, arr.len() as int) + arr.subrange(0, (arr.len() - k) as int)
    }
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error by removing extra brace in check_all_rotations */
proof fn lemma_rotate_right_properties(arr: Seq<int>, k: int)
    requires 0 <= k < arr.len()
    ensures rotate_right(arr, k).len() == arr.len()
{
}

proof fn lemma_empty_is_sorted()
    ensures is_sorted(Seq::<int>::empty())
{
}

proof fn lemma_single_is_sorted(x: int)
    ensures is_sorted(seq![x])
{
}

fn check_all_rotations(arr: &Vec<i8>) -> (result: bool)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j]
    ensures
        result == true <==> exists|k: int| #[trigger] is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), k)) && 0 <= k < arr.len()
{
    if arr.len() == 0 {
        return true;
    }
    
    let mut rotation: usize = 0;
    while rotation < arr.len()
        invariant
            0 <= rotation <= arr.len(),
            forall|k: int| 0 <= k < rotation ==> !is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), k))
    {
        proof {
            let rotated_seq = rotate_right(arr@.map(|i, x: i8| x as int), rotation as int);
            if is_sorted(rotated_seq) {
                return true;
            }
        }
        rotation += 1;
    }
    false
}

fn check_sorted(seq: &Seq<int>) -> (result: bool)
    ensures result == is_sorted(*seq)
{
    if seq.len() <= 1nat {
        return true;
    }
    
    let mut i: usize = 0;
    while i < seq.len() - 1nat
        invariant
            0 <= i <= seq.len() - 1nat,
            forall|j: int, k: int| 0 <= j < k < i + 1 ==> seq[j] <= seq[k]
    {
        proof {
            let ghost curr_val = seq[i as int];
            let ghost next_val = seq[(i + 1) as int];
            if curr_val > next_val {
                return false;
            }
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn move_one_ball(arr: Vec<i8>) -> (result: bool)
    requires 
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i as int] != arr[j as int]
    ensures 
        arr.len() == 0 ==> result == true,
        result == true ==> (arr.len() == 0 || exists|k: int| #[trigger] is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), k)) && 0 <= k < arr.len()),
        result == false ==> forall|k: int| 0 <= k < arr.len() ==> !is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), k))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax error by removing extra brace */
    if arr.len() == 0 {
        return true;
    }
    
    let mut rotation: usize = 0;
    while rotation < arr.len()
        invariant
            0 <= rotation <= arr.len(),
            forall|k: int| 0 <= k < rotation ==> !is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), k))
    {
        let ghost rotated_seq = rotate_right(arr@.map(|i, x: i8| x as int), rotation as int);
        
        let mut is_rotation_sorted = true;
        let mut i: usize = 0;
        while i < arr.len() - 1nat
            invariant
                0 <= i <= arr.len() - 1nat,
                is_rotation_sorted == forall|j: int| 0 <= j < i ==> rotated_seq[j] <= rotated_seq[j + 1]
        {
            let ghost curr_idx = ((arr.len() as int - rotation as int + i as int) % arr.len() as int) as usize;
            let ghost next_idx = ((arr.len() as int - rotation as int + i as int + 1) % arr.len() as int) as usize;
            
            if arr[curr_idx] > arr[next_idx] {
                is_rotation_sorted = false;
                break;
            }
            i += 1;
        }
        
        if is_rotation_sorted {
            return true;
        }
        
        rotation += 1;
    }
    false
}
// </vc-code>


}

fn main() {}