// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
}

spec fn can_communicate(a: int, b: int, c: int, d: int) -> bool {
    (if a - c >= 0 { a - c } else { c - a }) <= d || 
    (((if a - b >= 0 { a - b } else { b - a }) <= d) && 
     ((if b - c >= 0 { b - c } else { c - b }) <= d))
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_abs_i16_int_equiv(a: i16, b: i16)
    requires
        1 <= a as int <= 100,
        1 <= b as int <= 100,
    ensures
        (if a >= b { (a - b) as int } else { (b - a) as int }) ==
        (if a as int - b as int >= 0 { a as int - b as int } else { b as int - a as int }),
{
    if a >= b {
        assert(a as int - b as int >= 0);
        assert(a as int - b as int <= 99);
        assert(((a - b) as int) == (a as int - b as int));
    } else {
        assert(b as int - a as int >= 0);
        assert(b as int - a as int <= 99);
        assert(((b - a) as int) == (b as int - a as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int, c as int, d as int),
    ensures 
        result@ == seq!['Y', 'e', 's'] <==> can_communicate(a as int, b as int, c as int, d as int),
        result@ == seq!['Y', 'e', 's'] || result@ == seq!['N', 'o'],
// </vc-spec>
// <vc-code>
{
    let ai: i16 = a as i16;
    let bi: i16 = b as i16;
    let ci: i16 = c as i16;
    let di: i16 = d as i16;

    let abs_ac: i16 = if ai >= ci { ai - ci } else { ci - ai };
    let abs_ab: i16 = if ai >= bi { ai - bi } else { bi - ai };
    let abs_bc: i16 = if bi >= ci { bi - ci } else { ci - bi };

    let cond_exec: bool = (abs_ac as int) <= di as int
        || ((abs_ab as int) <= di as int && (abs_bc as int) <= di as int);

    proof {
        assert((ai as int) == (a as int));
        assert((bi as int) == (b as int));
        assert((ci as int) == (c as int));
        assert((di as int) == (d as int));

        lemma_abs_i16_int_equiv(ai, ci);
        lemma_abs_i16_int_equiv(ai, bi);
        lemma_abs_i16_int_equiv(bi, ci);

        let abs_ac_int: int = if ai >= ci { (ai - ci) as int } else { (ci - ai) as int };
        let abs_ab_int: int = if ai >= bi { (ai - bi) as int } else { (bi - ai) as int };
        let abs_bc_int: int = if bi >= ci { (bi - ci) as int } else { (ci - bi) as int };

        assert(abs_ac_int == (if a as int - c as int >= 0 { a as int - c as int } else { c as int - a as int }));
        assert(abs_ab_int == (if a as int - b as int >= 0 { a as int - b as int } else { b as int - a as int }));
        assert(abs_bc_int == (if b as int - c as int >= 0 { b as int - c as int } else { c as int - b as int }));

        assert((abs_ac as int) == abs_ac_int);
        assert((abs_ab as int) == abs_ab_int);
        assert((abs_bc as int) == abs_bc_int);

        assert(cond_exec == can_communicate(a as int, b as int, c as int, d as int));
    }

    if cond_exec {
        String::from("Yes")
    } else {
        String::from("No")
    }
}
// </vc-code>


}

fn main() {}