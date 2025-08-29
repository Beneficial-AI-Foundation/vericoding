use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn lemma_filter_extend<T>(s: Seq<T>, pred: spec_fn(T) -> bool, elem: T)
    ensures
        s.push(elem).filter(pred) == if pred(elem) {
            s.filter(pred).push(elem)
        } else {
            s.filter(pred)
        }
{
    /* code modified by LLM (iteration 5): added proof by induction on sequence length */
    if s.len() == 0 {
        assert(s.push(elem) =~= seq![elem]);
        assert(s.filter(pred) =~= seq![]);
    } else {
        let s_tail = s.subrange(1, s.len() as int);
        lemma_filter_extend(s_tail, pred, elem);
        assert(s.push(elem) =~= seq![s[0]].add(s_tail.push(elem)));
    }
}

proof fn lemma_subrange_extend<T>(s: Seq<T>, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1) == s.subrange(0, i).push(s[i])
{
}

proof fn lemma_subrange_full<T>(s: Seq<T>)
    ensures s.subrange(0, s.len() as int) == s
{
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    // pre-conditions-start
    requires 
        old(y).len() == 0,
    // pre-conditions-end
    // post-conditions-start
    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): added final proof block to establish postcondition */
    for i in 0..x.len()
        invariant
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
    {
        proof {
            lemma_subrange_extend(x@, i as int);
            lemma_filter_extend(x@.subrange(0, i as int), |k:u64| k%3 == 0, x@[i as int]);
        }
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
    }
    proof {
        lemma_subrange_full(x@);
    }
}
// </vc-code>

}

fn main() {}