use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_zero(a: &[i32]) -> (index: i32)
    requires
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 0,
        forall|i: int| 0 < i < a.len() ==> #[trigger] a[i-1] - 1 <= a[i],
    ensures
        (index < 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != 0),
        (0 <= index ==> index < a.len() && a[index as int] == 0),
// </vc-spec>
// <vc-code>
{
    let mut low: nat = 0;
    let mut high: nat = (a.len() as nat).overflowing_sub(1).unwrap_or(0);
    let mut result: int = -1;

    if a.len() == 0 {
        return -1;
    }

    while low <= high
        invariant
            low as int >= 0,
            high as int >= -1, // high can be -1 if a.len() is 0 or it goes below 0
            high as int <= a.len() as int - 1,
            result == -1 || (result as nat) < (a.len() as nat) && a[result as nat] == 0, // result must remain -1 until the element is found or points to a valid zero
            forall|i: int| 0 <= i < low as int ==> a[i] > 0,
            forall|i: int| high as int + 1 <= i < a.len() ==> a[i] > 0,
            low as int <= high as int + 1,
            a.len() >= 0,
    {
        let mid: nat = low + (high - low) / 2;

        if a[mid as nat] == 0 {
            result = mid as int;
            if mid == 0 {
                break;
            }
            high = mid - 1; // Try to find an earlier zero
        } else if a[mid as nat] > 0 {
            if mid == 0 { // If mid is 0 and a[0] > 0, then no zero exists before or at 0
                break;
            }
            high = mid - 1;
        } else {
            // This case should not happen given the precondition a[i] >= 0
            // If it ever does, move the low pointer to continue search
            low = mid + 1;
        }
    }
    result as i32
}
// </vc-code>

fn main() {}

}