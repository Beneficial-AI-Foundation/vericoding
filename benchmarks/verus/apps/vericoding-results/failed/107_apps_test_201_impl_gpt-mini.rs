// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(c: int, hr: int, hb: int, wr: int, wb: int) -> bool {
    c >= 0 && hr > 0 && hb > 0 && wr > 0 && wb > 0
}

spec fn valid_candy_combination(red_count: int, blue_count: int, c: int, wr: int, wb: int) -> bool {
    red_count >= 0 && blue_count >= 0 && red_count * wr + blue_count * wb <= c
}

spec fn joy(red_count: int, blue_count: int, hr: int, hb: int) -> int {
    red_count * hr + blue_count * hb
}
// </vc-preamble>

// <vc-helpers>
spec fn blue_max(c: int, red: int, wr: int, wb: int) -> int
    requires
        c >= 0,
        red >= 0,
        wr > 0,
        wb > 0,
        red * wr <= c,
    ensures
        result >= 0,
        red * wr + result * wb <= c,
        forall|b: int| b >= 0 && red * wr + b * wb <= c ==> b <= result,
{
    (c - red * wr) / wb
}
// </vc-helpers>

// <vc-spec>
fn solve(c: i8, hr: i8, hb: i8, wr: i8, wb: i8) -> (result: i8)
    requires
        valid_input(c as int, hr as int, hb as int, wr as int, wb as int),
    ensures
        result >= 0,
        exists|red_count: int, blue_count: int| 
            valid_candy_combination(red_count, blue_count, c as int, wr as int, wb as int) &&
            result as int == joy(red_count, blue_count, hr as int, hb as int),
        forall|red_count: int, blue_count: int|
            valid_candy_combination(red_count, blue_count, c as int, wr as int, wb as int) ==>
            joy(red_count, blue_count, hr as int, hb as int) <= result as int,
// </vc-spec>
// <vc-code>
{
    let c_int = c as int;
    let hr_i = hr as int;
    let hb_i = hb as int;
    let wr_i = wr as int;
    let wb_i = wb as int;

    let mut best_joy: int = 0;
    let mut best_red: int = 0;
    let mut best_blue: int = 0;

    let max_red = c_int / wr_i;
    let mut red: int = 0;
    while red <= max_red
        invariant
            0 <= red,
            red <= max_red + 1,
            best_joy >= 0,
            forall|r: int| 0 <= r && r < red ==> r * hr_i + blue_max(c_int, r, wr_i, wb_i) * hb_i <= best_joy,
        decreases
            max_red - red
    {
        let b = blue_max(c_int, red, wr_i, wb_i);
        let cur = red * hr_i + b * hb_i;
        if cur > best_joy {
            best_joy = cur;
            best_red = red;
            best_blue = b;
        }
        red = red + 1;
    }

    proof {
        // After the loop, red == max_red + 1
        assert(red == max_red + 1);
        // best_red and best_blue are the witness for the maximal joy
        // Prove feasibility of the chosen counts
        // best_red <= max_red because it was always assigned with red <= max_red
        assert(best_red <= max_red);
        assert(best_red >= 0);
        // therefore best_red * wr_i <= max_red * wr_i <= c_int
        assert(best_red * wr_i <= c_int);
        // best_blue was obtained via blue_max when best_red was assigned, so feasibility holds
        assert(best_red * wr_i + best_blue * wb_i <= c_int);
        // best_joy equals the joy of best_red and best_blue by construction
        assert(best_joy == best_red * hr_i + best_blue * hb_i);

        // Optimality: for any feasible (rc, bc) show joy(rc,bc) <= best_joy
        forall|rc: int, bc: int|
            if rc >= 0 && bc >= 0 && rc * wr_i + bc * wb_i <= c_int {
                // rc <= max_red because rc * wr_i <= c_int and max_red = c_int / wr_i
                assert(rc <= max_red);
                // since rc < red (red = max_red + 1), the loop invariant gives
                assert(rc * hr_i + blue_max(c_int, rc, wr_i, wb_i) * hb_i <= best_joy);
                // blue_max guarantees bc <= blue_max(c_int, rc, wr_i, wb_i)
                assert(bc <= blue_max(c_int, rc, wr_i, wb_i));
                // hb_i > 0 from precondition valid_input, so increasing blue increases joy
                assert(rc * hr_i + bc * hb_i <= rc * hr_i + blue_max(c_int, rc, wr_i, wb_i) * hb_i);
                assert(rc * hr_i + bc * hb_i <= best_joy);
            }
    }

    // Return the best joy as i8. The specification requires existence of a matching
    // integer-valued joy; here best_joy satisfies that and is returned.
    best_joy as i8
}
// </vc-code>


}

fn main() {}