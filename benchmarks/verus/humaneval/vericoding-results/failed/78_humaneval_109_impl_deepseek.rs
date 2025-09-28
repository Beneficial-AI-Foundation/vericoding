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
/* helper modified by LLM (iteration 5): Add lemma for map conversion and fix compilation */
proof fn lemma_map_i8_to_int(arr: Vec<i8>) -> (s: Seq<int>)
    ensures
        s == arr@.map(|i, x| x as int),
        s.len() == arr.len()
{
    reveal_with_fuel(seq::map_spec, 2);
    arr@.map(|i, x: i8| x as int)
}

proof fn lemma_rotate_right_eq_identity(arr: Seq<int>, k: int)
    requires
        0 <= k <= arr.len(),
    ensures
        #[trigger] rotate_right(arr, k) == seq::new(arr.len(), |i: int| {
            if i < k {
                arr[arr.len() - k + i]
            } else {
                arr[i - k]
            }
        })
{
}

proof fn lemma_sorted_after_rotate(arr: Seq<int>, k: int)
    requires
        0 <= k <= arr.len(),
        is_sorted(rotate_right(arr, k)),
    ensures
        forall|i: int| k <= i < arr.len() - 1 ==> arr[i] <= arr[i + 1],
        forall|i: int| 0 <= i < k - 1 ==> arr[i] <= arr[i + 1],
        arr.len() > 0 ==> arr[arr.len() - 1] <= arr[0]
{
}

proof fn lemma_all_equal_if_sorted_and_cyclic(arr: Seq<int>)
    requires
        arr.len() > 0,
        is_sorted(arr),
        arr[arr.len() - 1] <= arr[0],
    ensures
        forall|i: int| 0 <= i < arr.len() ==> arr[i] == arr[0]
{
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
    /* code modified by LLM (iteration 5): Fix compilation error by using proper sequence conversion */
    if arr.len() == 0 {
        return true;
    }
    
    proof {
        let arr_int = lemma_map_i8_to_int(arr);
        let mut min_val = arr_int[0];
        let mut min_index: int = 0;
        let mut j: int = 1;
        while j < arr_int.len()
            invariant
                1 <= j <= arr_int.len(),
                min_val == arr_int[min_index],
                0 <= min_index < j,
                forall|k: int| 0 <= k < j ==> arr_int[min_index] <= arr_int[k],
        {
            if arr_int[j] < min_val {
                min_val = arr_int[j];
                min_index = j;
            }
            j = j + 1;
        }
        
        let rotated = rotate_right(arr_int, min_index);
        
        if rotated.len() > 0 {
            let mut sorted = true;
            let mut k: int = 0;
            while k < rotated.len() - 1
                invariant
                    0 <= k <= rotated.len() - 1,
                    sorted == (forall|l: int| 0 <= l < k ==> rotated[l] <= rotated[l + 1])
            {
                if rotated[k] > rotated[k + 1] {
                    sorted = false;
                    break;
                }
                k = k + 1;
            }
            
            if sorted {
                assert(is_sorted(rotated));
                true
            } else {
                false
            }
        } else {
            true
        }
    }
}
// </vc-code>


}

fn main() {}