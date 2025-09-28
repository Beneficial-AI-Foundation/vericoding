// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(m: int, b: int) -> bool {
  1 <= m <= 1000 && 1 <= b <= 10000
}

spec fn f(x: int, y: int) -> int {
  (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2
}

spec fn valid_rectangle_corner(k: int, m: int, b: int) -> bool {
  0 <= k && b - k >= 0
}

spec fn rectangle_value(k: int, m: int, b: int) -> int {
  f(k * m, b - k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove rectangle_value nonneg */
proof fn rectangle_value_nonneg(k: int, m: int, b: int)
    requires
        valid_rectangle_corner(k, m, b),
        m >= 0,
    ensures
        rectangle_value(k, m, b) >= 0,
{
    proof {
        reveal(rectangle_value);
        reveal(f);
        let x = k * m;
        let y = b - k;
        assert(x >= 0);
        assert(y >= 0);
        assert(x * (x + 1) * (y + 1) >= 0);
        assert(y * (y + 1) * (x + 1) >= 0);
        assert((x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2 >= 0);
    }
}

/* helper modified by LLM (iteration 5): relate rectangle_value to its arithmetic definition */
proof fn rectangle_value_def(k: int, m: int, b: int)
    ensures
        (let x = k * m, y = b - k; (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2) == rectangle_value(k, m, b),
{
    proof {
        reveal(rectangle_value);
        reveal(f);
        let x = k * m;
        let y = b - k;
        assert(rectangle_value(k, m, b) == (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(m: i8, b: i8) -> (result: i8)
  requires 
    valid_input(m as int, b as int)
  ensures 
    result as int >= -1,
    forall|k: int| valid_rectangle_corner(k, m as int, b as int) ==> result as int >= rectangle_value(k, m as int, b as int),
    exists|k: int| valid_rectangle_corner(k, m as int, b as int) && result as int == rectangle_value(k, m as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement exhaustive search for maximal rectangle value */
    let mi = m as int;
    let bi = b as int;

    let mut k: int = 0;
    let mut arg: int = 0;
    let mut best: int = {
        let x = 0 * mi;
        let y = bi - 0;
        (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2
    };

    while k <= bi
        invariant
            0 <= k && k <= bi + 1,
            0 <= arg && arg <= bi,
            forall|i: int| 0 <= i < k ==> rectangle_value(i, mi, bi) <= best,
            best == rectangle_value(arg, mi, bi),
        decreases
            bi + 1 - k
    {
        let x = k * mi;
        let y = bi - k;
        let val = (x * (x + 1) * (y + 1) + y * (y + 1) * (x + 1)) / 2;
        proof {
            assert(0 <= k && bi - k >= 0);
            rectangle_value_def(k, mi, bi);
            assert(val == rectangle_value(k, mi, bi));
        }

        if val > best {
            best = val;
            arg = k;
        }
        k = k + 1;
    }

    proof {
        assert(k == bi + 1);
        assert(forall|i: int| 0 <= i <= bi ==> rectangle_value(i, mi, bi) <= best);
        assert(forall|i: int| valid_rectangle_corner(i, mi, bi) ==> best >= rectangle_value(i, mi, bi));
        assert(valid_rectangle_corner(arg, mi, bi));
        assert(best == rectangle_value(arg, mi, bi));
    }

    (best as i8)
}

// </vc-code>


}

fn main() {}