use vstd::prelude::*;

verus! {

spec fn abs_spec(i: int) -> int {
    if i < 0 { -i } else { i }
}

// <vc-helpers>
// <vc-helpers>
/* No additional helpers needed */
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
// <vc-code>
{
    // impl-start
    let n: usize = numbers.len();
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut wi: int = 0;
    let mut wj: int = 0;

    while i < n
        invariant 0 <= i as int && i as int <= n as int,
        invariant forall|a: int, b: int| (0 <= a && a < i as int && 0 <= b && b < n as int && a != b) ==>
            !(#[trigger] abs_spec((numbers[a as usize] as int) - (numbers[b as usize] as int)) < (threshold as int))
    {
        let mut j: usize = i + 1;
        while j < n
            invariant i < n,
            invariant j >= i + 1 && j <= n,
            invariant forall|b: int| (0 <= b && b < j as int) ==>
                !(#[trigger] abs_spec((numbers[i as usize] as int) - (numbers[b as usize] as int)) < (threshold as int))
        {
            let ni: int = numbers[i] as int;
            let nj: int = numbers[j] as int;
            let diff: int = ni - nj;
            let absd: int = if diff < 0 { -diff } else { diff };
            if absd < (threshold as int) {
                found = true;
                wi = i as int;
                wj = j as int;
                break;
            }
            j += 1;
        }

        if found {
            break;
        }

        i += 1;
    }

    if found {
        proof {
            // witnesses are wi and wj
            assert(0 <= wi && wi < n as int);
            assert(0 <= wj && wj < n as int);
            assert(wi != wj);
            assert(#[trigger] abs_spec((numbers[wi as usize] as int) - (numbers[wj as usize] as int)) < (threshold as int));
            assert(exists|a: int, b: int|
                0 <= a && 0 <= b && a < n as int && b < n as int && a != b &&
                #[trigger] abs_spec((numbers[a as usize] as int) - (numbers[b as usize] as int)) < (threshold as int)
            );
        }
        true
    } else {
        proof {
            // loop invariant at exit gives that for all a < n and b < n, no close pair exists
            assert(!(i < n));
            assert(i as int >= n as int);
            assert(i as int <= n as int);
            assert(i as int == n as int);
            assert(forall|a: int, b: int|
                0 <= a && a < n as int && 0 <= b && b < n as int && a != b ==>
                    !(#[trigger] abs_spec((numbers[a as usize] as int) - (numbers[b as usize] as int)) < (threshold as int))
            );
            assert(!exists|a: int, b: int|
                0 <= a && 0 <= b && a < n as int && b < n as int && a != b &&
                #[trigger] abs_spec((numbers[a as usize] as int) - (numbers[b as usize] as int)) < (threshold as int)
            );
        }
        false
    }
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}