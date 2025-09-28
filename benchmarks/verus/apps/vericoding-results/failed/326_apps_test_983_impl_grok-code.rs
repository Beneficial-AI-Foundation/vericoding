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
/* helper modified by LLM (iteration 5): Added executable versions of max_prefix and max_seq to support the main logic */
fn exec_max_prefix(s: &Vec<i32>, i: usize) -> i32 {
    let mut max_val = s[0];
    for j in 0..=i {
        if s[j] > max_val {
            max_val = s[j];
        }
    }
    max_val
}

fn exec_max_seq(s: &Vec<i32>) -> i32 {
    let mut max_val = s[0];
    for &val in s {
        if val > max_val {
            max_val = val;
        }
    }
    max_val
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, q: i8, r: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|i, x| x as int))
    ensures result as int == max_expression(n as int, p as int, q as int, r as int, a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implemented the computation of s1, s2, s3 using executable helpers */
    let n_usize = n as usize;
    let mut s1 = Vec::with_capacity(n_usize);
    for i in 0..n_usize {
        s1.push((a[i] as i32) * (p as i32));
    }
    let mut s2 = Vec::with_capacity(n_usize);
    for i in 0..n_usize {
        let m = exec_max_prefix(&s1, i);
        s2.push(m + (a[i] as i32) * (q as i32));
    }
    let mut s3 = Vec::with_capacity(n_usize);
    for i in 0..n_usize {
        let m = exec_max_prefix(&s2, i);
        s3.push(m + (a[i] as i32) * (r as i32));
    }
    let result_val = exec_max_seq(&s3);
    result_val as i8
}
// </vc-code>


}

fn main() {}