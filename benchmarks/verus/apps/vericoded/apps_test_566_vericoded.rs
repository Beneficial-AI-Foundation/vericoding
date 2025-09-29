// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int, g: int, b: int) -> bool {
    r >= 0 && g >= 0 && b >= 0
}

spec fn max_tables(r: int, g: int, b: int) -> int
    recommends valid_input(r, g, b)
{
    min(min(min((r + g + b) / 3, r + g), r + b), g + b)
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_min_le_left(a: int, b: int)
    ensures
        min(a, b) <= a,
{
    if a <= b {
        assert(min(a, b) == a);
    } else {
        assert(min(a, b) == b);
        assert(b <= a);
    }
}

proof fn lemma_min_le_right(a: int, b: int)
    ensures
        min(a, b) <= b,
{
    if a <= b {
        assert(min(a, b) == a);
        assert(a <= b);
    } else {
        assert(min(a, b) == b);
    }
}

proof fn lemma_min_nonneg(a: int, b: int)
    requires
        a >= 0,
        b >= 0,
    ensures
        min(a, b) >= 0,
{
    if a <= b {
        assert(min(a, b) == a);
    } else {
        assert(min(a, b) == b);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, g: i8, b: i8) -> (result: i8)
    requires 
        valid_input(r as int, g as int, b as int)
    ensures 
        result as int == max_tables(r as int, g as int, b as int),
        result >= 0
// </vc-spec>
// <vc-code>
{
    let ri: i16 = r as i16;
    let gi: i16 = g as i16;
    let bi: i16 = b as i16;

    proof {
        assert(ri as int == r as int);
        assert(gi as int == g as int);
        assert(bi as int == b as int);
        assert(0 <= r as int && r as int <= 127);
        assert(0 <= g as int && g as int <= 127);
        assert(0 <= b as int && b as int <= 127);
        assert((ri as int) + (gi as int) >= 0 && (ri as int) + (gi as int) <= 254);
        assert((ri as int) + (bi as int) >= 0 && (ri as int) + (bi as int) <= 254);
        assert((gi as int) + (bi as int) >= 0 && (gi as int) + (bi as int) <= 254);
    }

    let rg: i16 = ri + gi;
    let rb: i16 = ri + bi;
    let gb: i16 = gi + bi;

    proof {
        assert((rg as int) == (ri as int + gi as int));
        assert((rb as int) == (ri as int + bi as int));
        assert((gb as int) == (gi as int + bi as int));
        assert((rg as int) + (bi as int) >= 0 && (rg as int) + (bi as int) <= 381);
    }

    let sum: i16 = rg + bi;
    let three: i16 = 3;
    let a3: i16 = sum / three;

    let m1: i16 = if a3 <= rg { a3 } else { rg };
    let m2: i16 = if m1 <= rb { m1 } else { rb };
    let m3: i16 = if m2 <= gb { m2 } else { gb };

    proof {
        // Basic arithmetic alignment between machine ints and mathematical ints
        let rr: int = r as int;
        let gg: int = g as int;
        let bb: int = b as int;
        assert((sum as int) == (rg as int + bi as int));
        assert((sum as int) == (rr + gg + bb));
        assert((sum as int) >= 0);
        assert((sum as int) <= 381);
        assert((a3 as int) == (sum as int) / 3);
        assert((rg as int) == rr + gg);
        assert((rb as int) == rr + bb);
        assert((gb as int) == gg + bb);

        // Evaluate mins step by step in int domain
        assert(min(a3 as int, rg as int) == if (a3 as int) <= (rg as int) { a3 as int } else { rg as int });
        assert((a3 <= rg) == ((a3 as int) <= (rg as int)));
        assert((m1 as int) == if a3 <= rg { a3 as int } else { rg as int });
        assert((m1 as int) == min(a3 as int, rg as int));

        assert(min((m1 as int), (rb as int)) == if (m1 as int) <= (rb as int) { (m1 as int) } else { (rb as int) });
        assert((m1 <= rb) == ((m1 as int) <= (rb as int)));
        assert((m2 as int) == if m1 <= rb { (m1 as int) } else { (rb as int) });
        assert((m2 as int) == min((m1 as int), (rb as int)));

        assert(min((m2 as int), (gb as int)) == if (m2 as int) <= (gb as int) { (m2 as int) } else { (gb as int) });
        assert((m2 <= gb) == ((m2 as int) <= (gb as int)));
        assert((m3 as int) == if m2 <= gb { (m2 as int) } else { (gb as int) });
        assert((m3 as int) == min((m2 as int), (gb as int)));

        // Now connect to spec max_tables
        assert((m3 as int) == min(min(min((rr + gg + bb) / 3, rr + gg), rr + bb), gg + bb));

        // Bound m3 to be within [0, 127] for safe cast to i8
        // First, non-negativity of each component
        assert((a3 as int) >= 0);
        assert((rg as int) >= 0);
        assert((rb as int) >= 0);
        assert((gb as int) >= 0);
        // Use min nonneg repeatedly
        lemma_min_nonneg(a3 as int, rg as int);
        lemma_min_nonneg(min(a3 as int, rg as int), rb as int);
        lemma_min_nonneg(min(min(a3 as int, rg as int), rb as int), gb as int);
        // Upper bound via chaining min <= left
        lemma_min_le_left(a3 as int, rg as int);
        lemma_min_le_left(min(a3 as int, rg as int), rb as int);
        lemma_min_le_left(min(min(a3 as int, rg as int), rb as int), gb as int);
        assert((m3 as int) <= (a3 as int));
        assert((a3 as int) <= 127);
    }

    let res: i8 = m3 as i8;

    proof {
        let rr: int = r as int;
        let gg: int = g as int;
        let bb: int = b as int;
        assert((res as int) == (m3 as int));
        assert((res as int) == min(min(min((rr + gg + bb) / 3, rr + gg), rr + bb), gg + bb));
        assert((res as int) >= 0);
    }

    res
}
// </vc-code>


}

fn main() {}