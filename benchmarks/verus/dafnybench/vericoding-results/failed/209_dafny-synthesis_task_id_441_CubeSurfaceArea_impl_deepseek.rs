use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn cube_surface_area_lemma(size: nat)
    requires size > 0
    ensures 6 * size * size == 6 * (size * size)
{
    assert(size * size >= 0) by {
        assert(size > 0);
    };
    assert(6 * (size * size) == 6 * size * size) by (nonlinear_arith);
}

proof fn mul_bound_lemma(a: int, b: int, bound: int)
    requires
        a >= 0,
        b >= 0,
        a <= bound,
        b <= bound,
    ensures
        a * b <= bound * bound,
{
    if bound == 0 {
        assert(a == 0 && b == 0);
        assert(a * b == 0);
    } else {
        assert(a * b <= bound * bound) by (nonlinear_arith);
    }
}

proof fn max_safe_size_bound_lemma(size: int)
    requires
        size > 0,
        size <= 0x7FFFFFFFint / 6,
    ensures
        6 * size * size <= 0x7FFFFFFFint,
{
    let max_safe_size = 0x7FFFFFFFint / 6;
    assert(size <= max_safe_size);
    
    mul_bound_lemma(size, size, max_safe_size);
    assert(size * size <= max_safe_size * max_safe_size);
    
    assert(6 * size * size <= 6 * (max_safe_size * max_safe_size)) by (nonlinear_arith);
    assert(6 * (max_safe_size * max_safe_size) <= 0x7FFFFFFFint) by {
        assert(max_safe_size * max_safe_size <= (0x7FFFFFFFint / 6) * max_safe_size) by (nonlinear_arith);
        assert(6 * ((0x7FFFFFFFint / 6) * max_safe_size) == (6 * (0x7FFFFFFFint / 6)) * max_safe_size);
        assert(6 * (0x7FFFFFFFint / 6) <= 0x7FFFFFFFint);
        assert((6 * (0x7FFFFFFFint / 6)) * max_safe_size <= 0x7FFFFFFFint * max_safe_size);
        assert(0x7FFFFFFFint * max_safe_size <= 0x7FFFFFFFint * (0x7FFFFFFFint / 6));
        assert(6 * (max_safe_size * max_safe_size) <= 0x7FFFFFFFint) by (nonlinear_arith);
    };
}
// </vc-helpers>

// <vc-spec>
fn cube_surface_area(size: i32) -> (area: i32)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// <vc-code>
{
    proof {
        cube_surface_area_lemma(size as nat);
        assert(6 * (size * size) == 6 * size * size) by (nonlinear_arith);
        
        let max_safe_size: int = 0x7FFFFFFFint / 6;
        assert(size as int <= max_safe_size) by {
            assert(size > 0);
            assert(size as int > 0);
            assert(size as int <= 0x7FFFFFFFint / 6);
        };
        max_safe_size_bound_lemma(size as int);
    }
    assert(6 * size * size <= 0x7FFFFFFF) by {
        assert(6 * (size as int) * (size as int) <= 0x7FFFFFFFint);
    };
    let area = 6 * size * size;
    area
}
// </vc-code>

fn main() {
}

}