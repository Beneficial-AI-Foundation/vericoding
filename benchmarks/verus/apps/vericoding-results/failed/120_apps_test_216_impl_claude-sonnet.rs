// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_abs(arr: Seq<int>, i: int) -> int
    decreases arr.len() - i when 0 <= i <= arr.len()
{
    if i == arr.len() {
        0
    } else {
        (if arr[i] >= 0 { arr[i] } else { -arr[i] }) + sum_abs(arr, i + 1)
    }
}

spec fn valid_input(n: int, arr: Seq<int>) -> bool {
    0 <= n == arr.len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow checking lemmas for i8 arithmetic */
proof fn sum_abs_step(arr: Seq<int>, i: int)
    requires 0 <= i < arr.len()
    ensures sum_abs(arr, i) == (if arr[i] >= 0 { arr[i] } else { -arr[i] }) + sum_abs(arr, i + 1)
{
    // proof by definition unfolding
}

proof fn sum_abs_bounds(arr: Seq<int>, i: int)
    requires 0 <= i <= arr.len(),
             forall|j: int| 0 <= j < arr.len() ==> -128 <= arr[j] < 128
    ensures -128 * (arr.len() - i) <= sum_abs(arr, i) <= 127 * (arr.len() - i)
    decreases arr.len() - i
{
    if i == arr.len() {
        assert(sum_abs(arr, i) == 0);
    } else {
        sum_abs_bounds(arr, i + 1);
    }
}

proof fn neg_i8_safe(val: i8)
    requires val > -128
    ensures -val >= -127
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, arr: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, arr@.map(|i: int, v: i8| v as int))
    ensures result as int == sum_abs(arr@.map(|i: int, v: i8| v as int), 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow protection and invariant initialization */
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    
    proof {
        assert(i == 0);
        assert(sum == 0);
        assert(sum_abs(arr@.map(|j: int, v: i8| v as int), 0 as int) == sum_abs(arr@.map(|j: int, v: i8| v as int), i as int));
        sum_abs_bounds(arr@.map(|j: int, v: i8| v as int), 0);
    }
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            sum as int == sum_abs(arr@.map(|j: int, v: i8| v as int), i as int),
        decreases arr.len() - i
    {
        let val = arr[i];
        let abs_val = if val >= 0 { 
            val 
        } else { 
            proof {
                assert(val > -128);
                neg_i8_safe(val);
            }
            -val 
        };
        
        proof {
            sum_abs_step(arr@.map(|j: int, v: i8| v as int), i as int);
            assert(sum_abs(arr@.map(|j: int, v: i8| v as int), i as int) == 
                   abs_val as int + sum_abs(arr@.map(|j: int, v: i8| v as int), (i + 1) as int));
            sum_abs_bounds(arr@.map(|j: int, v: i8| v as int), (i + 1) as int);
            assert(sum as int + abs_val as int <= 127 * arr.len());
        }
        
        sum = sum + abs_val;
        i = i + 1;
    }
    
    sum
}
// </vc-code>


}

fn main() {}