#![crate_name = "max_segment_sum"]

use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn add(a: i64, b: i32) -> (result: i64)
    ensures
        result == a + b,
{
    return 0;  // TODO: Remove this line and implement the function body
}

spec fn sum(a: Seq<i32>, s: int, t: int) -> int
    decreases t - s,
{
    if s < 0 || s >= t || t > a.len() {
        0
    } else {
        a[t - 1] + sum(a, s, t - 1)
    }
}

#[verifier::loop_isolation(false)]
        ({ let (i, j) = p; 0 <= i <= j <= a.len() }),
        ({ let (i, j) = p; forall|k: int, l: int| 0 <= k <= l <= a.len() ==> sum(a@, k, l) <= sum(a@, i as int, j as int) })
{
    assume(
        forall|l: int, m: int, r: int| #![auto] 0 <= l <= m <= r <= a.len() ==>
            sum(a@, l, m) + sum(a@, m, r) == sum(a@, l, r)
    );

    let mut ans_l = 0;
    let mut ans_r = 0;
    let mut cur_l = 0;

    let mut ans_sum = 0;
    let mut cur_sum: i64 = 0;

    let mut pos = 0;
    while pos < a.len()
        invariant
            0 <= cur_l <= pos <= a.len(),
            cur_sum == sum(a@, cur_l as int, pos as int),
            0 <= cur_sum,

            forall|r: int| cur_l <= r <= pos ==> sum(a@, cur_l as int, r) >= 0,
            forall|b: int| 0 <= b <= pos ==> sum(a@, b, pos as int) <= sum(a@, cur_l as int, pos as int),

            0 <= ans_l <= ans_r <= pos,
            ans_sum == sum(a@, ans_l as int, ans_r as int),
            // forall|p: int, q: int| 0 <= p <= q <= pos ==> sum(a@, p, q) <= sum(a@, ans_l as int, ans_r as int),
    {
        cur_sum = add(cur_sum, a[pos]);
        pos += 1;
        if cur_sum < 0 {
            cur_l = pos;
            cur_sum = 0;
        } else if ans_sum < cur_sum {
            ans_l = cur_l;
            ans_r = pos;
            ans_sum = cur_sum;
        }

        assert(forall|b: int| 0 <= b <= pos ==> sum(a@, b, pos as int) <= sum(a@, cur_l as int, pos as int)) by {
            assert(forall|b: int| 0 <= b <= pos ==>
                sum(a@, cur_l as int, pos as int) - sum(a@, b, pos as int) == sum(a@, b as int, cur_l as int)
            );
            assert(sum(a@, cur_l as int, pos as int) >= 0);
        };
    }
    (ans_l, ans_r)
}

fn main() {}
}
