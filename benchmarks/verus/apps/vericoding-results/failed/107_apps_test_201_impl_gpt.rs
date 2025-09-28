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
/* helper modified by LLM (iteration 2): division bound lemma to relate product bound to quotient bound */
proof fn lemma_div_bound(x: int, y: int, a: int)
    requires
        0 <= x,
        0 < y,
        0 <= a,
        a * y <= x,
    ensures
        a <= x / y,
{
}

/* helper modified by LLM (iteration 2): derive bounds on r and b from a valid combination */
proof fn lemma_valid_pair_bounds(c: int, wr: int, wb: int, r: int, b: int)
    requires
        c >= 0,
        wr > 0,
        wb > 0,
        valid_candy_combination(r, b, c, wr, wb),
    ensures
        0 <= r,
        0 <= b,
        r <= c / wr,
        b <= c / wb,
{
    // From valid_candy_combination we know r >= 0, b >= 0 and r*wr + b*wb <= c
    // Hence r*wr <= c and b*wb <= c, then apply lemma_div_bound
    lemma_div_bound(c, wr, r);
    lemma_div_bound(c, wb, b);
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
    /* code modified by LLM (iteration 2): replaced ghost ints with executable i32 counters and used spec casts in invariants */
    let ci: i32 = c as i32;
    let hri: i32 = hr as i32;
    let hbi: i32 = hb as i32;
    let wri: i32 = wr as i32;
    let wbi: i32 = wb as i32;

    let rmax: i32 = if wri > 0 { ci / wri } else { 0 };
    let bmax: i32 = if wbi > 0 { ci / wbi } else { 0 };

    let mut best: i32 = 0;
    let mut gr: i32 = 0;
    let mut gb: i32 = 0;

    let mut r: i32 = 0;
    while r <= rmax
        invariant
            0 <= (r as int),
            (r as int) <= (rmax as int) + 1,
            0 <= (rmax as int),
            0 <= (bmax as int),
            valid_input(c as int, hr as int, hb as int, wr as int, wb as int),
            (best as int) == joy(gr as int, gb as int, hr as int, hb as int),
            valid_candy_combination(gr as int, gb as int, c as int, wr as int, wb as int),
            forall|ri: int, bi: int|
                0 <= ri < (r as int) ==> 0 <= bi <= (bmax as int) ==>
                    valid_candy_combination(ri, bi, c as int, wr as int, wb as int) ==>
                    joy(ri, bi, hr as int, hb as int) <= (best as int),
        decreases (rmax as int) + 1 - (r as int)
    {
        let mut b: i32 = 0;
        while b <= bmax
            invariant
                0 <= (r as int),
                (r as int) <= (rmax as int),
                0 <= (b as int),
                (b as int) <= (bmax as int) + 1,
                0 <= (rmax as int),
                0 <= (bmax as int),
                valid_input(c as int, hr as int, hb as int, wr as int, wb as int),
                (best as int) == joy(gr as int, gb as int, hr as int, hb as int),
                valid_candy_combination(gr as int, gb as int, c as int, wr as int, wb as int),
                forall|ri: int, bi: int|
                    0 <= ri < (r as int) ==> 0 <= bi <= (bmax as int) ==>
                        valid_candy_combination(ri, bi, c as int, wr as int, wb as int) ==>
                        joy(ri, bi, hr as int, hb as int) <= (best as int),
                forall|bi: int|
                    0 <= bi < (b as int) ==>
                        valid_candy_combination(r as int, bi, c as int, wr as int, wb as int) ==>
                        joy(r as int, bi, hr as int, hb as int) <= (best as int),
            decreases (bmax as int) + 1 - (b as int)
        {
            if valid_candy_combination(r as int, b as int, c as int, wr as int, wb as int) {
                let j: i32 = r * hri + b * hbi;
                if j > best {
                    best = j;
                    gr = r;
                    gb = b;
                }
            }
            b = b + 1;
        }
        r = r + 1;
    }

    proof {
        // The chosen (gr, gb) is within bounds for any valid pair
        lemma_valid_pair_bounds(c as int, wr as int, wb as int, gr as int, gb as int);
    }

    let result_val: i8 = best as i8;
    result_val
}
// </vc-code>


}

fn main() {}