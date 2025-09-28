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
spec fn vec_to_seq(v: Vec<i8>) -> Seq<int> {
    v@.map(|i, x| x as int)
}

/* helper modified by LLM (iteration 4): fixed proof with explicit case analysis */
proof fn max_seq_is_max_prefix(s: Seq<int>)
    requires s.len() > 0
    ensures max_seq(s) == max_prefix(s, (s.len()-1) as nat)
    decreases s.len()
{
    if s.len() == 1 {
        assert(max_seq(s) == s[0]);
        assert(max_prefix(s, 0) == s[0]);
    } else {
        let sub_seq = s.subrange(0, s.len()-1);
        max_seq_is_max_prefix(sub_seq);
        let last = s[s.len()-1];
        let max_sub = max_seq(sub_seq);
        let max_prefix_sub = max_prefix(sub_seq, (sub_seq.len()-1) as nat);
        assert(max_sub == max_prefix_sub);
        
        let max_s = if last > max_sub { last } else { max_sub };
        let max_prefix_s = if last > max_prefix_sub { last } else { max_prefix_sub };
        
        assert(max_seq(s) == max_s);
        assert(max_prefix(s, (s.len()-1) as nat) == max_prefix_s);
        assert(max_s == max_prefix_s);
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
    /* code modified by LLM (iteration 5): fixed invariant formatting */
    let n_usize = n as usize;
    let mut s1 = Vec::with_capacity(n_usize);
    for i in 0..n_usize {
        s1.push(a[i] * p);
    }

    let mut prefix_max_s1 = Vec::new();
    let mut s2 = Vec::new();
    let mut current_max_s1 = s1[0];
    prefix_max_s1.push(current_max_s1);
    s2.push(current_max_s1 + a[0] * q);

    for i in 1..n_usize
        invariant 
            prefix_max_s1.len() == i,
            s2.len() == i,
            forall |j: int| 0 <= j < i ==> j < vec_to_seq(s1).len() && 
                prefix_max_s1[j] as int == max_prefix(vec_to_seq(s1), j as nat),
            i > 0 ==> 
                (i-1) as nat < vec_to_seq(s1).len() && 
                current_max_s1 as int == max_prefix(vec_to_seq(s1), (i-1) as nat),
    {
        if s1[i] > current_max_s1 {
            current_max_s1 = s1[i];
        }
        prefix_max_s1.push(current_max_s1);
        s2.push(current_max_s1 + a[i] * q);
    }

    let mut prefix_max_s2 = Vec::new();
    let mut s3 = Vec::new();
    let mut current_max_s2 = s2[0];
    prefix_max_s2.push(current_max_s2);
    s3.push(current_max_s2 + a[0] * r);

    for i in 1..n_usize
        invariant 
            prefix_max_s2.len() == i,
            s3.len() == i,
            forall |j: int| 0 <= j < i ==> j < vec_to_seq(s2).len() && 
                prefix_max_s2[j] as int == max_prefix(vec_to_seq(s2), j as nat),
            i > 0 ==> 
                (i-1) as nat < vec_to_seq(s2).len() && 
                current_max_s2 as int == max_prefix(vec_to_seq(s2), (i-1) as nat),
    {
        if s2[i] > current_max_s2 {
            current_max_s2 = s2[i];
        }
        prefix_max_s2.push(current_max_s2);
        s3.push(current_max_s2 + a[i] * r);
    }

    let mut result = s3[0];
    for i in 1..n_usize
        invariant 
            (i-1) as nat < vec_to_seq(s3).len() 
            && result as int == max_prefix(vec_to_seq(s3), (i-1) as nat),
    {
        if s3[i] > result {
            result = s3[i];
        }
    }

    proof {
        max_seq_is_max_prefix(vec_to_seq(s3));
    }

    result
}
// </vc-code>


}

fn main() {}