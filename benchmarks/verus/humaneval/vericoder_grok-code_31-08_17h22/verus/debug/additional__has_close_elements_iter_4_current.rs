use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>
//
// </vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
    // pre-conditions-start
    requires
        threshold > 0,
        forall|i: int, j: int| 0 <= i && i < numbers.len() && 0 <= j && j < numbers.len() ==> numbers[i] - numbers[j] < i32::MAX && -(numbers[i] - numbers[j]) < i32::MAX
    // pre-conditions-end
    // post-conditions-start
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
    // post-conditions-end
// </vc-spec>
// <vc-code>
#[verifier::loop_isolation(false)]
fn has_close_elements(numbers: &[i32], threshold: i32) -> (flag: bool)
    // pre-conditions-start
    requires
        threshold > 0,
        forall|i: int, j: int| 0 <= i && i < numbers.len() && 0 <= j && j < numbers.len() ==> numbers[i] - numbers[j] < i32::MAX && -(numbers[i] - numbers[j]) < i32::MAX
    // pre-conditions-end

    // post-conditions-start
    ensures
        flag == exists|i: int, j: int| 0 <= i && 0 <= j && i < numbers.len() && j < numbers.len() && i != j && abs_spec(numbers[i] - numbers[j]) < threshold
    // post-conditions-end
{
let len = numbers.len();
let mut flag = false;
for i in 0..len 
    invariant
        flag == exists|i2: int, j2: int| 0 <= i2 && 0 <= j2 && i2 < i && j2 < numbers@.len() && i2 != j2 && abs_spec(numbers@[i2] - numbers@[j2]) < threshold
{
  for j in 0..len 
    invariant
        flag == exists|i2: int, j2: int| 0 <= i2 && 0 <= j2 && i2 < len && (i2 < i || (i2 == i && j2 < j)) && j2 < numbers@.len() && i2 != j2 && abs_spec(numbers@[i2] - numbers@[j2]) < threshold
  {
    if i != j 
    {
      let a = numbers[i] as i64;
      let b = numbers[j] as i64;
      let diff = a - b;
      let abs_diff_i64 = diff.abs();
      if abs_diff_i64 < (threshold as i64) {
        proof { assert(abs_spec(numbers@[i] - numbers@[j]) < threshold); }
        flag = true;
      }
    }
  }
}
flag
}
// </vc-code>

fn main() {}
}