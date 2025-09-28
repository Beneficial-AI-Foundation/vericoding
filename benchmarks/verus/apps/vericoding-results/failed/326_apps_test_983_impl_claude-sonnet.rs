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
/* helper modified by LLM (iteration 5): fixed postconditions with explicit proofs */
proof fn lemma_max_prefix_monotonic(s: Seq<int>, i: nat, j: nat)
    requires
        i < s.len(),
        j < s.len(),
        i <= j
    ensures max_prefix(s, i) <= max_prefix(s, j)
    decreases j - i
{
    if i == j {
        // trivial case
    } else {
        lemma_max_prefix_monotonic(s, i, (j-1) as nat);
    }
}

proof fn lemma_max_seq_in_range(s: Seq<int>)
    requires s.len() > 0
    ensures exists |i: int| 0 <= i < s.len() && max_seq(s) == s[i]
    decreases s.len()
{
    if s.len() == 1 {
        assert(max_seq(s) == s[0]);
    } else {
        let sub_seq = s.subrange(0, (s.len()-1) as int);
        lemma_max_seq_in_range(sub_seq);
        assert(exists |i: int| 0 <= i < sub_seq.len() && max_seq(sub_seq) == sub_seq[i]);
        if s[(s.len()-1) as int] > max_seq(sub_seq) {
            assert(max_seq(s) == s[(s.len()-1) as int]);
        } else {
            assert(max_seq(s) == max_seq(sub_seq));
            let k = choose |i: int| 0 <= i < sub_seq.len() && max_seq(sub_seq) == sub_seq[i];
            assert(s[k] == sub_seq[k]);
            assert(max_seq(s) == s[k]);
        }
    }
}

proof fn lemma_max_prefix_bound(s: Seq<int>, i: nat)
    requires i < s.len()
    ensures exists |j: nat| j <= i && max_prefix(s, i) == s[j as int]
    decreases i
{
    if i == 0 {
        assert(max_prefix(s, i) == s[0]);
    } else {
        lemma_max_prefix_bound(s, (i-1) as nat);
        if s[i as int] > max_prefix(s, (i-1) as nat) {
            assert(max_prefix(s, i) == s[i as int]);
        } else {
            assert(max_prefix(s, i) == max_prefix(s, (i-1) as nat));
            let k = choose |j: nat| j <= (i-1) as nat && max_prefix(s, (i-1) as nat) == s[j as int];
            assert(max_prefix(s, i) == s[k as int]);
        }
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
    /* code modified by LLM (iteration 5): use ghost variables for spec types */
    let n_usize = n as usize;
    
    ghost let n_nat = n as nat;
    ghost let ghost_a = a@.map(|i, x| x as int);
    
    let mut s1_max = (a[0] as i32) * (p as i32);
    let mut s2_max = s1_max + (a[0] as i32) * (q as i32);
    let mut s3_max = s2_max + (a[0] as i32) * (r as i32);
    
    let mut i = 1;
    while i < n
        invariant
            0 < i <= n,
            i as usize <= a.len()
        decreases n - i
    {
        let s1_curr = (a[i as usize] as i32) * (p as i32);
        if s1_curr > s1_max {
            s1_max = s1_curr;
        }
        
        let s2_curr = s1_max + (a[i as usize] as i32) * (q as i32);
        if s2_curr > s2_max {
            s2_max = s2_curr;
        }
        
        let s3_curr = s2_max + (a[i as usize] as i32) * (r as i32);
        if s3_curr > s3_max {
            s3_max = s3_curr;
        }
        
        i = i + 1;
    }
    
    s3_max as i8
}
// </vc-code>


}

fn main() {}