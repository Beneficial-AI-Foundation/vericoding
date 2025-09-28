// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(arr: Seq<int>, k: int) -> bool {
  1 <= arr.len() <= 100 && 1 <= k <= arr.len()
}

spec fn sum_valid_elements(arr: Seq<int>, k: int) -> int {
  sum_valid_elements_up_to(arr, k)
}

spec fn sum_valid_elements_up_to(arr: Seq<int>, n: int) -> int
  decreases n
{
  if n == 0 {
    0int
  } else if 0 <= n-1 < arr.len() {
    let current = if -99 <= arr[n-1] <= 99 { arr[n-1] } else { 0int };
    sum_valid_elements_up_to(arr, n-1) + current
  } else {
    0int
  }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `Seq::new` signature expects a `usize` for length. The anonymous function in `Seq::new` takes a `usize`, not `nat`. The `update` method on `Seq` takes a `usize`, not `nat`. The `tracked_val_at` method on `Vec` expects a `usize`, not `nat`. Corrected all these type inconsistencies to address the compilation errors. The invariant in the helper function was updated to use `j as usize` to match `v.tracked_val_at`'s expected type. */
fn vec_to_seq_int(v: &Vec<i8>) -> (s: Seq<int>)
    ensures s.len() == v.len()
{
    let mut s = Seq::new(v.len(), |i: usize| 0int);
    let mut i = 0usize;
    while i < v.len()
        invariant 
            0 <= i <= v.len(),
            s.len() == v.len(),
            forall |j: usize| 0 <= j < i ==> s.index(j) == v.tracked_val_at(j) as int,
    {
        s = s.update(i, v.tracked_val_at(i) as int);
        i = i + 1;
    }
    s
}
// </vc-helpers>

// <vc-spec>
fn add_elements(arr: Vec<i8>, k: i8) -> (result: i8)
  requires valid_input(arr@.map(|i: int, x: i8| x as int), k as int)
  ensures result as int == sum_valid_elements(arr@.map(|i: int, x: i8| x as int), k as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No change */
{
    let arr_seq = vec_to_seq_int(&arr);
    let mut sum: i8 = 0;
    let mut i: usize = 0;

    while i < k as usize
        invariant
            0 <= i as int <= k as int,
            sum as int == sum_valid_elements_up_to(arr_seq, i as int),
            valid_input(arr_seq, k as int),
        decreases k as int - i as int
    {
        let val = arr[i];
        if -99 <= val && val <= 99 {
            sum = sum + val;
        }
        i = i + 1;
    }
    sum
}
// </vc-code>


}

fn main() {}