// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Provide precise bounds and results for floor division cases */
proof fn lemma_deg2rad_pos_0(di: int)
    requires
        0 <= di <= 57,
    ensures
        di * 314int / 18000int == 0int,
{
    assert(57int * 314int == 17898int);
    assert(0int <= di * 314int);
    assert(di * 314int <= 17898int);
    assert(0int / 18000int == 0int);
    assert(17898int / 18000int == 0int);
    assert(0int <= (di * 314int) / 18000int);
    assert((di * 314int) / 18000int <= 0int);
}

/* helper modified by LLM (iteration 5): Provide precise bounds and results for floor division cases */
proof fn lemma_deg2rad_pos_1(di: int)
    requires
        58 <= di <= 114,
    ensures
        di * 314int / 18000int == 1int,
{
    assert(58int * 314int == 18212int);
    assert(114int * 314int == 35796int);
    assert(18212int <= di * 314int);
    assert(di * 314int <= 35796int);
    assert(18212int / 18000int == 1int);
    assert(35796int / 18000int == 1int);
    assert(1int <= (di * 314int) / 18000int);
    assert((di * 314int) / 18000int <= 1int);
}

/* helper modified by LLM (iteration 5): Provide precise bounds and results for floor division cases */
proof fn lemma_deg2rad_pos_2(di: int)
    requires
        115 <= di <= 127,
    ensures
        di * 314int / 18000int == 2int,
{
    assert(115int * 314int == 36110int);
    assert(127int * 314int == 39878int);
    assert(36110int <= di * 314int);
    assert(di * 314int <= 39878int);
    assert(36110int / 18000int == 2int);
    assert(39878int / 18000int == 2int);
    assert(2int <= (di * 314int) / 18000int);
    assert((di * 314int) / 18000int <= 2int);
}

/* helper modified by LLM (iteration 5): Correct negative small-magnitude case to -1 using floor division */
proof fn lemma_deg2rad_neg_m1(di: int)
    requires
        -57 <= di <= -1,
    ensures
        di * 314int / 18000int == -1int,
{
    assert(57int * 314int == 17898int);
    assert(-17898int <= di * 314int);
    assert(di * 314int <= -314int);
    assert((-17898int) / 18000int == -1int);
    assert((-314int) / 18000int == -1int);
    assert(-1int <= (di * 314int) / 18000int);
    assert((di * 314int) / 18000int <= -1int);
}

/* helper modified by LLM (iteration 5): Correct negative mid-range case to -2 using floor division */
proof fn lemma_deg2rad_neg_m2(di: int)
    requires
        -114 <= di <= -58,
    ensures
        di * 314int / 18000int == -2int,
{
    assert(114int * 314int == 35796int);
    assert(58int * 314int == 18212int);
    assert(-35796int <= di * 314int);
    assert(di * 314int <= -18212int);
    assert((-35796int) / 18000int == -2int);
    assert((-18212int) / 18000int == -2int);
    assert(-2int <= (di * 314int) / 18000int);
    assert((di * 314int) / 18000int <= -2int);
}

/* helper modified by LLM (iteration 5): Add case for most negative values to -3 using floor division */
proof fn lemma_deg2rad_neg_m3(di: int)
    requires
        -128 <= di <= -115,
    ensures
        di * 314int / 18000int == -3int,
{
    assert(128int * 314int == 40192int);
    assert(115int * 314int == 36110int);
    assert(-40192int <= di * 314int);
    assert(di * 314int <= -36110int);
    assert((-40192int) / 18000int == -3int);
    assert((-36110int) / 18000int == -3int);
    assert(-3int <= (di * 314int) / 18000int);
    assert((di * 314int) / 18000int <= -3int);
}
// </vc-helpers>

// <vc-spec>
fn deg2rad(degrees: Vec<i8>) -> (radians: Vec<i8>)
    ensures 
        radians.len() == degrees.len(),
        forall|i: int| 0 <= i < degrees.len() ==> #[trigger] radians@[i] as int == degrees@[i] as int * 314 / 18000
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Strengthen decreases proof with explicit assertions and invariants */
    let n: usize = degrees.len();
    let mut radians: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let ghost n_int: int = n as int;

    while i < n
        invariant
            0 <= i <= n,
            n == degrees.len(),
            i <= degrees.len(),
            i as int <= n_int,
            radians.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] radians@[j] as int == degrees@[j] as int * 314int / 18000int,
        decreases n_int - i as int
    {
        let d: i8 = degrees[i];
        let out: i8 = if d >= 0 {
            if d <= 57i8 { 0 } else if d <= 114i8 { 1 } else { 2 }
        } else {
            if d >= -57i8 { -1 } else if d >= -114i8 { -2 } else { -3 }
        };
        proof {
            let di: int = d as int;
            if di >= 0int {
                if di <= 57int {
                    lemma_deg2rad_pos_0(di);
                    assert(out as int == 0int);
                } else if di <= 114int {
                    lemma_deg2rad_pos_1(di);
                    assert(out as int == 1int);
                } else {
                    lemma_deg2rad_pos_2(di);
                    assert(out as int == 2int);
                }
            } else {
                if di >= -57int {
                    lemma_deg2rad_neg_m1(di);
                    assert(out as int == -1int);
                } else if di >= -114int {
                    lemma_deg2rad_neg_m2(di);
                    assert(out as int == -2int);
                } else {
                    lemma_deg2rad_neg_m3(di);
                    assert(out as int == -3int);
                }
            }
            assert(out as int == di * 314int / 18000int);
        }
        radians.push(out);
        proof {
            assert(radians@[i as int] as int == out as int);
            let di: int = d as int;
            assert(radians@[i as int] as int == di * 314int / 18000int);
        }
        proof {
            assert(i < n);
            assert(i + 1 <= n);
            assert(((i + 1) as int) == i as int + 1);
            assert(n_int - ((i + 1) as int) < n_int - (i as int));
        }
        i = i + 1;
    }

    radians
}
// </vc-code>


}
fn main() {}