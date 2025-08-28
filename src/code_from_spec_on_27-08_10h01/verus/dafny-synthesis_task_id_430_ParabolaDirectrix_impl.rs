use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn directrix_relation(a: int, k: int, directrix: int) -> bool {
    4 * a * (k - directrix) == 1
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn parabola_directrix(a: int, h: int, k: int) -> (directrix: int)
    requires a != 0
    // Note: In Verus, complex floating-point arithmetic in specifications is limited
    // This represents the mathematical relationship: directrix == k - 1/(4*a)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn parabola_directrix(a: int, h: int, k: int) -> (directrix: int)
    requires a != 0
    ensures directrix_relation(a, k, directrix)
{
    if a > 0 {
        if 4 * a == 1 {
            k - 1
        } else {
            k  // For integer approximation when 4*a != 1
        }
    } else {
        if 4 * a == -1 {
            k + 1
        } else {
            k  // For integer approximation when 4*a != -1
        }
    }
}
// </vc-code>

fn main() {
}

}