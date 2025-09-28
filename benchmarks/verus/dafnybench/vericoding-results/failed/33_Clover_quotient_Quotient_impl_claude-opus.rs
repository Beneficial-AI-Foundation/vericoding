use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
proof fn quotient(x: nat, y: nat) -> (result: (int, int))
    requires y != 0
    ensures ({
        let (r, q) = result;
        q * y + r == x && 0 <= r < y && 0 <= q
    })
// </vc-spec>
// <vc-code>
{
    let q = (x / y) as int;
    let r = (x % y) as int;
    
    // Verus provides these properties for nat division and modulo
    assert(0 <= x % y < y);
    assert(x / y >= 0);
    
    // Use Verus's euclidean division lemma
    // For natural numbers, Verus knows: x == (x / y) * y + (x % y)
    // But we need to be more explicit about the types
    assert(x as int == (x / y) as int * y as int + (x % y) as int);
    
    // Now show that q * y + r == x
    assert(q == (x / y) as int);
    assert(r == (x % y) as int);
    assert(q * y + r == (x / y) as int * y as int + (x % y) as int);
    assert(q * y + r == x as int);
    assert(q * y + r == x);
    
    // Verify the bounds
    assert(0 <= r);
    assert(r < y);
    assert(0 <= q);
    
    (r, q)
}
// </vc-code>

fn main() {
}

}