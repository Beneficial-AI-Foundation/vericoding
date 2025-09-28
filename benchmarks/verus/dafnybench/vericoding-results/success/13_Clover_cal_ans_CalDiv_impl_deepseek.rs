use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn div_mod_lemma()
    ensures
        191i32 / 7i32 == 27i32,
        191i32 % 7i32 == 2i32,
{
    assert(7i32 * 27i32 == 189i32);
    assert(191i32 - 189i32 == 2i32);
    assert(2i32 < 7i32);
}
// </vc-helpers>

// <vc-spec>
fn cal_div() -> (result: (i32, i32))
  ensures result.0 == 191i32 / 7i32 && result.1 == 191i32 % 7i32,
// </vc-spec>
// <vc-code>
{
    proof {
        div_mod_lemma();
    }
    (27i32, 2i32)
}
// </vc-code>

fn main() {
}

}