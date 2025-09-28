// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(v: Seq<int>) -> int 
    decreases v.len()
{
    if v.len() == 0 { 
        0 
    } else if v.len() == 1 { 
        v[0] 
    } else { 
        v[0] + sum(v.subrange(1, v.len() as int))
    }
}

spec fn reverse<T>(s: Seq<T>) -> Seq<T> 
    decreases s.len()
{
    if s.len() == 0 { 
        seq![] 
    } else { 
        reverse(s.subrange(1, s.len() as int)).push(s[0])
    }
}

spec fn seq2set<T>(s: Seq<T>) -> Set<T> 
    decreases s.len()
{
    if s.len() == 0 { 
        set!{} 
    } else { 
        set!{s[0]}.union(seq2set(s.subrange(1, s.len() as int)))
    }
}

spec fn scalar_product(v1: Seq<int>, v2: Seq<int>) -> int
    decreases v1.len()
{
    if v1.len() == 0 || v2.len() == 0 { 
        0 
    } else { 
        v1[0] * v2[0] + scalar_product(v1.subrange(1, v1.len() as int), v2.subrange(1, v2.len() as int))
    }
}

fn multiplicity_examples<T>()
{
  assume(false);
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change to logic, just updating comment */
proof fn sum_append(s1: Seq<int>, s2: Seq<int>)
    ensures sum(s1 + s2) == sum(s1) + sum(s2)
    decreases s1.len()
{
    if s1.len() > 0 {
        sum_append(s1.subrange(1, s1.len() as int), s2);
    }
}
// </vc-helpers>

// <vc-spec>
fn vector_Sum(v: Seq<int>) -> (x: i32)
    ensures x == sum(v)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compile error by using correct sequence lemmas */
    let mut s: i32 = 0;
    let mut i: nat = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            s as int == sum(v.subrange(0, i as int)),
        decreases v.len() - i
    {
        proof {
            let sub = v.subrange(0, i as int);
            let next_sub = v.subrange(0, (i + 1) as int);
            let elem = seq![v[i as int]];
            assert(next_sub == sub + elem) by {
                vstd::seq_lib::subrange_concat(v, 0, i as int, (i + 1) as int);
                vstd::seq_lib::subrange_one(v, i as int);
            }
            sum_append(sub, elem);
        }
        let val = v[i] as i32;
        s = s + val;
        i = i + 1;
    }
    s
}
// </vc-code>

}
fn main() {}