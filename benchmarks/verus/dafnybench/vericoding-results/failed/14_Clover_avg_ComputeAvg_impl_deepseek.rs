use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn average_property(a: int, b: int)
    ensures (a + b) % 2 == 0 ==> (a + b) / 2 == (a + b) >> 1,
    ensures (a + b) % 2 != 0 ==> (a + b) / 2 == (a + b - 1) >> 1
{
    // Proof that for even sum: (a+b)/2 = (a+b) >> 1
    if (a + b) % 2 == 0 {
        assert((a + b) >> 1 == (a + b) / 2) by (bit_vector);
    }
    // Proof that for odd sum: (a+b)/2 = (a+b-1) >> 1
    if (a + b) % 2 != 0 {
        assert((a + b - 1) >> 1 == (a + b) / 2) by (bit_vector);
    }
}
// </vc-helpers>

// <vc-spec>
fn compute_avg(a: int, b: int) -> (avg: int)
    ensures avg == (a + b) / 2
// </vc-spec>
// <vc-code>
{
    let sum = a + b;
    proof { average_property(a, b); }
    if sum % 2 == 0 {
        (sum) >> 1
    } else {
        (sum - 1) >> 1
    }
}
// </vc-code>

fn main() {
}

}