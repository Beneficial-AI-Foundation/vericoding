use vstd::prelude::*;

verus! {

// <vc-helpers>
fn sum_partial(arr: &Vec<i32>, k: int) -> (ret: i32)
    requires
        0 <= k <= arr.len() as int,
    ensures
        ret == arr.subsequence(0, k as usize).fold(0, |acc, i| acc + i),
{
    let mut s: i32 = 0;
    let mut i: int = 0;
    while i < k
        invariant
            0 <= i <= k,
            s == arr.subsequence(0, i as usize).fold(0, |acc, j| acc + j),
    {
        s = s + arr.get(i as usize).unwrap();
        i = i + 1;
    }
    s
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < (result.0.len() - 1) as int ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == true ==> exists|i: int| 1 <= i <= operations.len() as int && result.0[i] < 0,
        result.1 == false ==> forall|i: int| 0 <= i < result.0.len() as int ==> result.0[i] >= 0,
// </vc-spec>
// <vc-code>
{
    let mut result_vec = Vec::<i32>::new();
    result_vec.push(0);

    let mut found_below_zero = false;
    let mut current_sum = 0;
    let mut i: int = 0;

    while i < (operations.len() as int)
        invariant
            0 <= i <= operations.len() as int,
            result_vec.len() == (i + 1) as usize,
            result_vec@[0] == 0,
            forall|j: int| 0 <= j < i ==> result_vec@[j + 1] == result_vec@[j] + operations@[j],
            current_sum == result_vec@[i],
            found_below_zero == (exists|k: int| 1 <= k <= i && result_vec@[k] < 0),
    {
        current_sum = current_sum + operations.get(i as usize).unwrap();
        result_vec.push(current_sum);

        proof {
            assert(result_vec.len() == (i + 2) as usize);
            assert(result_vec@[i + 1] == current_sum);
            assert(current_sum == result_vec@[i] + operations@[i]);
        }
        
        if current_sum < 0 {
            found_below_zero = true;
        }
        i = i + 1;
    }

    (result_vec, found_below_zero)
}
// </vc-code>

fn main() {}

}