use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>
// No helpers needed for this proof.
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
{
    let n: usize = numbers.len();
    let mut i: usize = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant forall|a: int, b: int|
            0 <= a && a < i as int && 0 <= b && b < n as int ==>
                !(a != b && abs_spec((numbers[a as usize] as int) - (numbers[b as usize] as int)) < threshold as int)
    {
        let mut j: usize = i + 1;
        while j < n
            invariant i < n
            invariant 0 <= j && j <= n
            invariant forall|a: int, b: int|
                0 <= a && a < i as int && 0 <= b && b < n as int ==>
                    !(a != b && abs_spec((numbers[a as usize] as int) - (numbers[b as usize] as int)) < threshold as int)
            invariant forall|b: int|
                0 <= b && b < j as int ==>
                    !(i as int != b && abs_spec((numbers[i as usize] as int) - (numbers[b as usize] as int)) < threshold as int)
        {
            let diff: int = (numbers[i] as int) - (numbers[j] as int);
            if abs_spec(diff) < threshold as int {
                proof {
                    assert(exists|a: int, b: int|
                        a == i as int &&
                        b == j as int &&
                        0 <= a && 0 <= b &&
                        a < n as int && b < n as int &&
                        a != b &&
                        abs_spec((numbers[a as usize] as int) - (numbers[b as usize] as int)) < threshold as int);
                }
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assert(forall|a: int, b: int|
            0 <= a && a < n as int && 0 <= b && b < n as int ==>
                !(a != b && abs_spec((numbers[a as usize] as int) - (numbers[b as usize] as int)) < threshold as int));
        assert(!exists|a: int, b: int|
            0 <= a && 0 <= b && a < n as int && b < n as int &&
            a != b &&
            abs_spec((numbers[a as usize] as int) - (numbers[b as usize] as int)) < threshold as int);
    }
    false
}
// </vc-code>

fn main() {}
}