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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, p: i8, q: i8, r: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|i, x| x as int))
    ensures result as int == max_expression(n as int, p as int, q as int, r as int, a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added n >= 0 check, proper bounds checks, and overflow handling */
    assert(n > 0);  // From precondition
    
    let mut s1: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n as usize
        invariant
            n > 0,
            i <= n as usize,
            s1@.len() == i as int,
            a@.len() == n as int,
            forall |j: int| 0 <= j < i as int ==> s1@[j] == (a@[j] as int * p as int) as i64,
        decreases n as usize - i
    {
        assert(i < a@.len());
        let val = (a[i] as i64).checked_mul(p as i64).unwrap();
        s1.push(val);
        i = i + 1;
    }
    
    assert(s1@.len() == n as int);
    assert(s1@.len() > 0);
    
    let mut s2: Vec<i64> = Vec::new();
    let mut max_s1: i64 = s1[0];
    let q_val = (a[0] as i64).checked_mul(q as i64).unwrap();
    s2.push(max_s1.checked_add(q_val).unwrap());
    
    let mut i: usize = 1;
    while i < n as usize
        invariant
            n > 0,
            1 <= i <= n as usize,
            s1@.len() == n as int,
            s2@.len() == i as int,
            a@.len() == n as int,
            max_s1 >= s1@[0],
            forall |j: int| 0 <= j < i as int ==> j < s1@.len(),
            forall |j: int| 0 <= j < i as int ==> max_s1 >= s1@[j],
        decreases n as usize - i
    {
        assert(i < s1@.len());
        if s1[i] > max_s1 {
            max_s1 = s1[i];
        }
        assert(i < a@.len());
        let q_val = (a[i] as i64).checked_mul(q as i64).unwrap();
        let val = max_s1.checked_add(q_val).unwrap();
        s2.push(val);
        i = i + 1;
    }
    
    assert(s2@.len() == n as int);
    assert(s2@.len() > 0);
    
    let mut s3: Vec<i64> = Vec::new();
    let mut max_s2: i64 = s2[0];
    let r_val = (a[0] as i64).checked_mul(r as i64).unwrap();
    s3.push(max_s2.checked_add(r_val).unwrap());
    
    let mut i: usize = 1;
    while i < n as usize
        invariant
            n > 0,
            1 <= i <= n as usize,
            s2@.len() == n as int,
            s3@.len() == i as int,
            a@.len() == n as int,
            max_s2 >= s2@[0],
            forall |j: int| 0 <= j < i as int ==> j < s2@.len(),
            forall |j: int| 0 <= j < i as int ==> max_s2 >= s2@[j],
        decreases n as usize - i
    {
        assert(i < s2@.len());
        if s2[i] > max_s2 {
            max_s2 = s2[i];
        }
        assert(i < a@.len());
        let r_val = (a[i] as i64).checked_mul(r as i64).unwrap();
        let val = max_s2.checked_add(r_val).unwrap();
        s3.push(val);
        i = i + 1;
    }
    
    assert(s3@.len() == n as int);
    assert(s3@.len() > 0);
    
    let mut max_s3: i64 = s3[0];
    let mut i: usize = 1;
    while i < n as usize
        invariant
            n > 0,
            1 <= i <= n as usize,
            s3@.len() == n as int,
            max_s3 >= s3@[0],
            forall |j: int| 0 <= j < i as int ==> j < s3@.len(),
            forall |j: int| 0 <= j < i as int ==> max_s3 >= s3@[j],
        decreases n as usize - i
    {
        assert(i < s3@.len());
        if s3[i] > max_s3 {
            max_s3 = s3[i];
        }
        i = i + 1;
    }
    
    max_s3 as i8
}
// </vc-code>


}

fn main() {}