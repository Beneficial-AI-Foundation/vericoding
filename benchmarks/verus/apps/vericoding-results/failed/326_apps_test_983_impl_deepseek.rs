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

proof fn lemma_max_prefix_monotonic(s: Seq<int>, i: nat, j: nat)
    requires
        i <= j,
        j < s.len(),
    ensures
        max_prefix(s, i) <= max_prefix(s, j),
    decreases j - i
{
    if i < j {
        lemma_max_prefix_monotonic(s, i, (j-1) as nat);
        assert(max_prefix(s, (j-1) as nat) <= max_prefix(s, j));
    }
}

proof fn lemma_max_seq_equals_last_prefix(s: Seq<int>)
    requires
        s.len() > 0,
    ensures
        max_seq(s) == max_prefix(s, (s.len()-1) as nat),
    decreases s.len()
{
    if s.len() == 1 {
        assert(max_seq(s) == s[0]);
        assert(max_prefix(s, 0) == s[0]);
    } else {
        let sub_seq = s.subrange(0, (s.len()-1) as int);
        lemma_max_seq_equals_last_prefix(sub_seq);
        
        if s[(s.len()-1) as int] > max_seq(sub_seq) {
            assert(max_seq(s) == s[(s.len()-1) as int]);
        } else {
            assert(max_seq(s) == max_seq(sub_seq));
        }
        
        assert(max_prefix(s, (s.len()-1) as nat) == {
            if s[(s.len()-1) as int] > max_prefix(s, (s.len()-2) as nat) {
                s[(s.len()-1) as int]
            } else {
                max_prefix(s, (s.len()-2) as nat)
            }
        });
        
        lemma_max_prefix_monotonic(s, (s.len()-2) as nat, (s.len()-1) as nat);
    }
}

proof fn lemma_max_prefix_expression_equivalence(s1: Seq<int>, s2: Seq<int>, i: nat)
    requires
        i < s1.len(),
        i < s2.len(),
        s1.len() == s2.len(),
        forall|k: nat| k <= i ==> s2[k] == max_prefix(s1, k),
    ensures
        max_prefix(s2, i) == max_prefix(s1, i),
    decreases i
{
    if i > 0 {
        lemma_max_prefix_expression_equivalence(s1, s2, (i-1) as nat);
    }
}

/* helper modified by LLM (iteration 5): Fixed sequence mapping syntax and ghost function */
proof fn lemma_casting_properties(seq_i8: Seq<i8>) -> (seq_int: Seq<int>)
    ensures
        seq_int == seq_i8.map(|x: i8| x as int),
        seq_int.len() == seq_i8.len()
{
    seq_i8.map(|x: i8| x as int)
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, q: i8, r: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|i, x| x as int))
    ensures result as int == max_expression(n as int, p as int, q as int, r as int, a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type issues with casting and vector operations */
    let mut s1: Vec<int> = Vec::with_capacity(n as usize);
    let mut s2: Vec<int> = Vec::with_capacity(n as usize);
    let mut s3: Vec<int> = Vec::with_capacity(n as usize);
    
    let mut i: usize = 0;
    while i < n as usize
        invariant
            i <= n as usize,
            s1@.len() == i,
            s2@.len() == i,
            s3@.len() == i,
            forall|k: nat| k < i ==> s1@[k] == (a@[k as int] as int) * (p as int),
            forall|k: nat| k < i ==> s2@[k] == max_prefix(s1@, k as nat) + (a@[k as int] as int) * (q as int),
            forall|k: nat| k < i ==> s3@[k] == max_prefix(s2@, k as nat) + (a@[k as int] as int) * (r as int),
    {
        let a_val = a[i] as int;
        
        let s1_val = a_val * (p as int);
        s1.push(s1_val);
        
        proof {
            if i > 0 {
                lemma_max_prefix_monotonic(s1@, (i-1) as nat, i as nat);
            }
        }
        
        let s2_val = if i == 0 {
            max_prefix(s1@, 0) + a_val * (q as int)
        } else {
            let prev_max = max_prefix(s1@, (i-1) as nat);
            prev_max + a_val * (q as int)
        };
        s2.push(s2_val);
        
        proof {
            if i > 0 {
                lemma_max_prefix_monotonic(s2@, (i-1) as nat, i as nat);
            }
        }
        
        let s3_val = if i == 0 {
            max_prefix(s2@, 0) + a_val * (r as int)
        } else {
            let prev_max = max_prefix(s2@, (i-1) as nat);
            prev_max + a_val * (r as int)
        };
        s3.push(s3_val);
        
        i += 1;
    }
    
    proof {
        lemma_max_seq_equals_last_prefix(s3@);
    }
    
    (max_prefix(s3@, (n as usize - 1) as nat) as i8)
}
// </vc-code>


}

fn main() {}