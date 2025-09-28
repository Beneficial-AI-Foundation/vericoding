// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn monotonic(l: Seq<int>) -> bool {
    if l.len() <= 1 {
        true
    } else {
        let increasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] <= l[(i + 1) as int];
        let decreasing = forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] >= l[(i + 1) as int];
        increasing || decreasing
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma parameter types to use Vec<i8> instead of int */
proof fn lemma_monotonic_increasing(l: Seq<int>)
    requires
        l.len() > 1,
        forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] <= l[(i + 1) as int],
    ensures
        monotonic(l),
{
}

proof fn lemma_monotonic_decreasing(l: Seq<int>)
    requires
        l.len() > 1,
        forall|i: nat| #![trigger l[i as int]] i < l.len() - 1 ==> l[i as int] >= l[(i + 1) as int],
    ensures
        monotonic(l),
{
}

proof fn lemma_cast_preserves_order(a: i8, b: i8)
    ensures
        a <= b <==> (a as int) <= (b as int),
        a >= b <==> (a as int) >= (b as int),
{
}
// </vc-helpers>

// <vc-spec>
fn is_monotonic(l: Vec<i8>) -> (result: bool)
    ensures result == monotonic(l@.map(|_i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type error by using vector element access correctly */
    if l.len() <= 1 {
        return true;
    }
    
    let mut is_increasing = true;
    let mut is_decreasing = true;
    
    let mut i = 0;
    while i < l.len() - 1
        invariant
            i <= l.len() - 1,
            is_increasing ==> forall|j: nat| #![trigger l@[j as int]] j < i ==> (l@[j as int] as int) <= (l@[(j + 1) as int] as int),
            is_decreasing ==> forall|j: nat| #![trigger l@[j as int]] j < i ==> (l@[j as int] as int) >= (l@[(j + 1) as int] as int),
        decreases l.len() - 1 - i
    {
        proof {
            lemma_cast_preserves_order(l@[i as int], l@[(i + 1) as int]);
        }
        
        if l[i] > l[i + 1] {
            is_increasing = false;
        }
        if l[i] < l[i + 1] {
            is_decreasing = false;
        }
        i += 1;
    }
    
    let result = is_increasing || is_decreasing;
    
    proof {
        let int_seq = l@.map(|_i: int, x: i8| x as int);
        
        if is_increasing {
            assert(forall|j: nat| #![trigger l@[j as int]] j < l.len() - 1 ==> (l@[j as int] as int) <= (l@[(j + 1) as int] as int));
            assert(forall|j: nat| #![trigger int_seq[j as int]] j < int_seq.len() - 1 ==> int_seq[j as int] <= int_seq[(j + 1) as int]);
            lemma_monotonic_increasing(int_seq);
        }
        
        if is_decreasing {
            assert(forall|j: nat| #![trigger l@[j as int]] j < l.len() - 1 ==> (l@[j as int] as int) >= (l@[(j + 1) as int] as int));
            assert(forall|j: nat| #![trigger int_seq[j as int]] j < int_seq.len() - 1 ==> int_seq[j as int] >= int_seq[(j + 1) as int]);
            lemma_monotonic_decreasing(int_seq);
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}