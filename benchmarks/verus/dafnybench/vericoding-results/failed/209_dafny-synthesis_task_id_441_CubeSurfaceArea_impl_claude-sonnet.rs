use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_cube_surface_area_bound(size: i32)
    requires size > 0 && size <= 18724
    ensures 6 * size * size <= i32::MAX
{
    assert(size <= 18724);
    assert(size * size <= size * 18724);
    assert(size * 18724 <= 18724 * 18724);
    assert(size * size <= 18724 * 18724);
    assert(18724 * 18724 == 350588176);
    assert(6 * size * size <= 6 * 350588176);
    assert(6 * 350588176 == 2103529056);
    assert(2103529056 <= i32::MAX);
}

proof fn lemma_i32_max_bound()
    ensures i32::MAX >= 2147483647
{
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
        assert(size > 0);
        if size <= 18724 {
            lemma_cube_surface_area_bound(size);
        } else {
            lemma_i32_max_bound();
            assert(size > 18724);
            assert(size >= 18725);
            assert(size * size >= 18725 * 18725);
            assert(18725 * 18725 == 350625625);
            assert(6 * size * size >= 6 * 350625625);
            assert(6 * 350625625 == 2103753750);
            assert(2103753750 > i32::MAX);
        }
    }
    6 * size * size
}
// </vc-code>

fn main() {
}

}