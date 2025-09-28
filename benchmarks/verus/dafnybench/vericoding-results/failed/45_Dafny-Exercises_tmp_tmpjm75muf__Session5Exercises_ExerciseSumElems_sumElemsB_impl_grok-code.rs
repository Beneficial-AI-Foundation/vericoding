use vstd::prelude::*;

verus! {

spec fn sum_r(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    }
}

spec fn sum_l(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_l(s.subrange(1, s.len() as int))
    }
}


spec fn sum_v(v: Seq<int>, c: int, f: int) -> int
{
    if 0 <= c <= f <= v.len() {
        sum_r(v.subrange(c, f))
    } else {
        0
    }
}

// <vc-helpers>
proof fn lemma_sum_r_snoc(s: Seq<int>, x: int) {
    decreases s.len()
    ensures sum_r(s) + x == sum_r(s.push(x))
    if s.len() == 0 {
    } else {
        lemma_sum_r_snoc(s.subrange(0, s.len() - 1), x);
        assert(sum_r(s) + x == sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1] + x);
        assert(sum_r(s.push(x)) == sum_r(s) + x);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_elems_b(v: &[i32]) -> (sum: i32)
//ensures sum as int == sum_l(v@.map(|i, x| x as int))
ensures sum as int == sum_r(v@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    let mut sum: int = 0;
    while i < v@.len() as nat
        invariant
            i <= v@.len() as nat,
            sum == sum_r(v@.map(|j: int, x: i32| x as int).subrange(0, i))
        decreases (v@.len() as nat - i)
    {
        proof {
            lemma_sum_r_snoc(v@.map(|j: int, x: i32| x as int).subrange(0, i), v@[i] as int);
        }
        sum = sum + (v@[i] as int);
        i = i + 1;
    }
    assert(sum == sum_r(v@.map(|j: int, x: i32| x as int)));
    (sum as i32)
}
// </vc-code>

fn main() {
}

}