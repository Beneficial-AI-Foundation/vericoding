// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_prefix(s: Seq<int>, i: nat) -> int
    recommends i < s.len()
    decreases i
{
    if i == 0 { s[0] }
    else if s[i as int] > max_prefix(s, (i-1) as nat) { s[i as int] }
    else { max_prefix(s, (i-1) as nat) }
}

spec fn max_seq(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 { s[0] }
    else {
        let sub_seq = s.subrange(0, (s.len()-1) as int);
        if s[(s.len()-1) as int] > max_seq(sub_seq) { s[(s.len()-1) as int] }
        else { max_seq(sub_seq) }
    }
}

spec fn max_expression(n: int, p: int, q: int, r: int, a: Seq<int>) -> int
    recommends n > 0 && a.len() == n
{
    let s1 = Seq::new(n as nat, |i: int| a[i] * p);
    let s2 = Seq::new(n as nat, |i: int| max_prefix(s1, i as nat) + a[i] * q);
    let s3 = Seq::new(n as nat, |i: int| max_prefix(s2, i as nat) + a[i] * r);
    max_seq(s3)
}

spec fn valid_input(n: int, a: Seq<int>) -> bool
{
    n > 0 && a.len() == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove max_seq equals max_prefix of last index */
proof fn max_seq_eq_prefix(s: Seq<int>)
    requires s.len() > 0
    ensures max_seq(s) == max_prefix(s, (s.len()-1) as nat)
    decreases s.len()
{
    if s.len() == 1 {
        // trivial: both return s[0]
    } else {
        let sub = s.subrange(0, (s.len()-1) as int);
        proof { max_seq_eq_prefix(sub); }
        // By definition of max_seq on s and max_prefix on s,
        // and the inductive hypothesis on sub, the equality holds
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, q: i8, r: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|i, x| x as int))
    ensures result as int == max_expression(n as int, p as int, q as int, r as int, a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute expression using runtime integers and prove equality */
    let n_usize: usize = n as usize;
    let p_i64: i64 = p as i64;
    let q_i64: i64 = q as i64;
    let r_i64: i64 = r as i64;

    let mut best1: i64 = (a[0] as i64) * p_i64; // corresponds to max_prefix(s1,0)
    let mut best2: i64 = best1 + (a[0] as i64) * q_i64; // corresponds to max_prefix(s2,0)
    let mut res_i: i64 = best2 + (a[0] as i64) * r_i64; // corresponds to max_prefix(s3,0)

    let mut idx: usize = 1;
    while idx < n_usize
        invariant
            idx <= n_usize,
            (idx > 0 ==> best1 as int == max_prefix(Seq::new(n as nat, |k: int| a@.map(|_,x| x as int)[k] * (p as int)), (idx-1) as nat)),
            (idx > 0 ==> best2 as int == max_prefix(Seq::new(n as nat, |k: int| max_prefix(Seq::new(n as nat, |i: int| a@.map(|_,x| x as int)[i] * (p as int)), k as nat) + a@.map(|_,x| x as int)[k] * (q as int)), (idx-1) as nat)),
            (idx > 0 ==> res_i as int == max_prefix(Seq::new(n as nat, |k: int| max_prefix(Seq::new(n as nat, |i: int| max_prefix(Seq::new(n as nat, |j: int| a@.map(|_,x| x as int)[j] * (p as int)), i as nat) + a@.map(|_,x| x as int)[i] * (q as int)), k as nat) + a@.map(|_,x| x as int)[k] * (r as int)), (idx-1) as nat)),
        decreases (n as nat) - (idx as nat)
    {
        let j: usize = idx;
        let ai_i8: i8 = a[j];
        let ai_i64: i64 = ai_i8 as i64;

        let s1val = ai_i64 * p_i64;
        if s1val > best1 {
            best1 = s1val;
        }

        let s2val = best1 + ai_i64 * q_i64;
        if s2val > best2 {
            best2 = s2val;
        }

        let s3val = best2 + ai_i64 * r_i64;
        if s3val > res_i {
            res_i = s3val;
        }

        idx = idx + 1;
    }

    proof {
        let n_nat: nat = n as nat;
        let p_int: int = p as int;
        let q_int: int = q as int;
        let r_int: int = r as int;
        let s1 = Seq::new(n_nat, |k: int| a@.map(|_,x| x as int)[k] * p_int);
        let s2 = Seq::new(n_nat, |k: int| max_prefix(s1, k as nat) + a@.map(|_,x| x as int)[k] * q_int);
        let s3 = Seq::new(n_nat, |k: int| max_prefix(s2, k as nat) + a@.map(|_,x| x as int)[k] * r_int);
        assert(res_i as int == max_prefix(s3, (n_nat - 1) as nat));
        max_seq_eq_prefix(s3);
        assert(res_i as int == max_seq(s3));
    }

    res_i as i8
}

// </vc-code>


}

fn main() {}