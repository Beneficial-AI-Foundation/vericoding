// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 0 && k >= 0 && k + 1 > 0
}

spec fn valid_output(result: Seq<int>, n: int, k: int) -> bool {
    result.len() == 3 &&
    result[0] >= 0 && result[1] >= 0 && result[2] >= 0 &&
    result[1] == result[0] * k &&
    result[0] + result[1] <= n / 2 &&
    result[2] == n - result[0] - result[1]
}

spec fn optimal_diplomas(n: int, k: int) -> int
    recommends valid_input(n, k)
{
    (n / 2) / (k + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): i8 bounds check */
fn i8_bounds(x: i8) {
    proof {
        assert(-128 <= x as int);
        assert(x as int <= 127);
    }
}

/* helper modified by LLM (iteration 5): compute optimal counts a0,a1,a2 from n,k */
spec fn compute_counts(n: int, k: int) -> (int, int, int) {
    let a0 = optimal_diplomas(n, k);
    let a1 = a0 * k;
    let a2 = n - a0 - a1;
    (a0, a1, a2)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, k as int)
    ensures 
        valid_output(result@.map(|i, x| x as int), n as int, k as int) &&
        result@[0] as int == optimal_diplomas(n as int, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute and pack diploma counts into Vec<i8> */
    // runtime computations using i32 to avoid overflow
    let ni: i32 = n as i32;
    let ki: i32 = k as i32;
    let a0_i: i32 = (ni / 2) / (ki + 1);
    let a1_i: i32 = a0_i * ki;
    let a2_i: i32 = ni - a0_i - a1_i;
    let x0: i8 = a0_i as i8;
    let x1: i8 = a1_i as i8;
    let x2: i8 = a2_i as i8;
    let mut v: Vec<i8> = Vec::new();
    v.push(x0);
    v.push(x1);
    v.push(x2);
    proof {
        i8_bounds(n);
        i8_bounds(k);
        let sn: int = n as int;
        let sk: int = k as int;
        let (sa0, sa1, sa2) = compute_counts(sn, sk);
        assert((ni as int) == sn);
        assert((ki as int) == sk);
        assert((ni / 2) as int == sn / 2);
        assert((ki + 1) as int == sk + 1);
        assert(a0_i as int == sa0);
        assert(a1_i as int == sa1);
        assert(a2_i as int == sa2);
        assert(v@.len() == 3);
        assert(v@[0] as int == sa0);
        assert(v@[1] as int == sa1);
        assert(v@[2] as int == sa2);
        assert(v@[0] as int == optimal_diplomas(sn, sk));
    }
    v
}
// </vc-code>


}

fn main() {}