// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn cube(n: int) -> int {
        n * n * n
}
    
    // </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove cube of equal ints are equal */
proof fn lemma_cube_eq_of_equal(a: int, b: int)
    requires
        a == b,
    ensures
        cube(a) == cube(b),
{
    assert(cube(a) == a * a * a);
    assert(cube(b) == b * b * b);
    assert(a * a * a == b * b * b);
}

// </vc-helpers>

// <vc-spec>
fn is_cube(n: u8) -> (r: bool)
    ensures r == exists|k: int| 0 <= k <= n as int && n as int == cube(k)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over u8 values and use proof blocks for int reasoning without creating int locals in executable code */
    let mut i: u8 = 0;
    while i <= n
        invariant
            0 <= i as int,
            i as int <= n as int + 1,
            forall |k: int| 0 <= k && k < i as int ==> n as int != cube(k),
        decreases
            (n as int) - i as int + 1
    {
        let cube_ki_u32: u32 = (i as u32) * (i as u32) * (i as u32);
        if cube_ki_u32 == (n as u32) {
            proof {
                let ki: int = i as int;
                assert(0 <= ki && ki <= n as int);
                // relate the runtime equality to the specification-level equality
                assert((cube_ki_u32 as int) == ki * ki * ki);
                assert(ki * ki * ki == cube(ki));
                assert((cube_ki_u32 as int) == (n as int));
                assert(cube(ki) == n as int);
            }
            return true;
        }
        i = i + 1;
    }
    proof {
        // from loop exit and invariant, i as int == n as int + 1
        assert(i as int > n as int);
        assert(i as int <= n as int + 1);
        assert(i as int == n as int + 1);
        assert(forall |k: int| 0 <= k && k < i as int ==> n as int != cube(k));
        assert(forall |k: int| 0 <= k && k <= n as int ==> n as int != cube(k));
        assert(!(exists |k: int| 0 <= k && k <= n as int && n as int == cube(k)));
    }
    return false;
}

// </vc-code>


}

fn main() {}