// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected the `fold` closure to accept `i32` for `acc` and `x`, and ensuring `numbers@[start + k as usize]` is cast to `int`. Moved `Seq::new` outside the `fold` lambda. Also fixed some `usize` to `int` and `i32` to `int` type mismatches. */
proof fn can_be_represented_as_sum_of_subarray_elements(numbers: &Vec<i32>, start: usize, end: usize, sum: i32)
    requires
        start <= end,
        end <= numbers.len(),
    ensures
        ( {
            let mut current_sum_local: i32 = 0;
            let mut k_local: nat = 0;
            while (k_local + start as nat) < end as nat
                invariant
                    k_local <= end as nat - start as nat,
                    current_sum_local as int == (Seq::new(k_local, |kk: nat| numbers@[start + kk as usize] as int)).fold(0, |acc: int, x: int| acc + x)
                decreases
                    end as nat - start as nat - k_local
            {
                current_sum_local = current_sum_local + numbers@[start + k_local as usize];
                k_local = k_local + 1;
            }
            current_sum_local == sum
        } )
{
    let mut current_sum_local: i32 = 0;
    let mut k_local: nat = 0;
    while (k_local + start as nat) < end as nat
        invariant
            k_local <= end as nat - start as nat,
            current_sum_local as int == (Seq::new(k_local, |kk: nat| numbers@[start + kk as usize] as int)).fold(0, |acc: int, x: int| acc + x)
        decreases
            end as nat - start as nat - k_local
    {
        current_sum_local = current_sum_local + numbers@[start + k_local as usize];
        k_local = k_local + 1;
    }
    assert(current_sum_local == sum);
}
// </vc-helpers>

// <vc-spec>
fn max_subarray_sum(numbers: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        forall|start: usize, end: usize| {
            start <= end && end <= numbers.len()
        } ==> {
            let mut subarray_sum: i32 = 0;
            subarray_sum <= result
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches (i32 vs. int, usize vs. int). Corrected the `fold` closure to accept `i32` for `acc` and `x`, and ensuring `numbers@[start_idx + k_val as usize]` is cast to `int`. Moved `Seq::new` outside the `fold` lambda. Removed `assume(false)` and `unreached()`. */
{
    let mut max_so_far: i32 = 0;
    let mut current_max: i32 = 0;
    let mut i: usize = 0;

    while i < numbers.len()
        invariant
            i <= numbers.len(),
            current_max >= 0,
            max_so_far >= current_max,
            forall|start_idx: usize, end_idx: usize| {
                start_idx <= end_idx && end_idx <= i
            } ==> {
                (end_idx >= start_idx ==> {
                    let seq_len = (end_idx - start_idx) as nat;
                    let sub_seq = Seq::new(seq_len, |k_val: nat| numbers@[start_idx + k_val as usize] as int);
                    sub_seq.fold(0, |acc: int, x: int| acc + x) <= max_so_far as int
                })
            },
        decreases
            numbers.len() - i
    {
        current_max = current_max + (numbers@[i] as i32);

        if current_max < 0 {
            current_max = 0;
        }

        if current_max > max_so_far {
            max_so_far = current_max;
        }
        i = i + 1;
    }
    max_so_far
}
// </vc-code>

}
fn main() {}