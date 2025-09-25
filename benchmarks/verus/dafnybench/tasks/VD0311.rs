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
// </vc-helpers>

// <vc-spec>
fn vector_Sum(v: Seq<int>) -> (x: i32)
    ensures x == sum(v)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}