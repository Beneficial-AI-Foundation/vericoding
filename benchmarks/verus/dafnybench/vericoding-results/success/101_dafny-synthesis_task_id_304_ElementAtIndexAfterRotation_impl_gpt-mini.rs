use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
proof fn element_at_index_after_rotation(l: Seq<int>, n: int, index: int) -> (element: int)
    requires 
        n >= 0,
        0 <= index < l.len(),
    ensures 
        element == l[((index - n + l.len() as int) % l.len() as int) as int],
// </vc-spec>
// <vc-code>
{
    let m: nat = l.len();
    // from 0 <= index < m we know m > 0
    assert(m > 0);
    let r_int: int = ((index - n + m as int) % m as int);
    // remainder properties for modulus with positive modulus
    assert(0 <= r_int);
    assert(r_int < m as int);
    let element: int = l.index(r_int);
    // relate computed element to the specification's index expression
    assert(element == l.index(r_int));
    assert(element == l[((index - n + l.len() as int) % l.len() as int) as int]);
    element
}
// </vc-code>

fn main() {
}

}