use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn lemma_filter_extend<T>(s: Seq<T>, elem: T, pred: spec_fn(T) -> bool)
    ensures s.push(elem).filter(pred) == 
        if pred(elem) { s.filter(pred).push(elem) } else { s.filter(pred) }
{
    /* code modified by LLM (iteration 5): added detailed proof steps to establish the filter property */
    let extended = s.push(elem);
    let filtered_extended = extended.filter(pred);
    let filtered_s = s.filter(pred);
    
    proof {
        assert(extended.len() == s.len() + 1);
        assert(extended[s.len()] == elem);
        
        if pred(elem) {
            assert forall |i: int| 0 <= i < filtered_s.len() implies 
                filtered_extended[i] == filtered_s[i] by {
                let filtered_count_s = s.len() - filtered_s.len();
                assert(filtered_extended[i] == filtered_s[i]);
            };
            assert(filtered_extended.len() == filtered_s.len() + 1);
            assert(filtered_extended[filtered_s.len()] == elem);
            assert(filtered_extended =~= filtered_s.push(elem));
        } else {
            assert forall |i: int| 0 <= i < filtered_s.len() implies 
                filtered_extended[i] == filtered_s[i];
            assert(filtered_extended.len() == filtered_s.len());
            assert(filtered_extended =~= filtered_s);
        }
    }
}

proof fn lemma_subrange_extend<T>(s: Seq<T>, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1) == s.subrange(0, i).push(s[i])
{
    let sub_i = s.subrange(0, i);
    let sub_i_plus_1 = s.subrange(0, i + 1);
    
    proof {
        assert(sub_i_plus_1.len() == sub_i.len() + 1);
        assert forall |j: int| 0 <= j < sub_i.len() implies 
            sub_i_plus_1[j] == sub_i[j];
        assert(sub_i_plus_1[i] == s[i]);
        assert(sub_i_plus_1 =~= sub_i.push(s[i]));
    }
}
// </vc-helpers>

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
    /* code modified by LLM (iteration 5): restructured proof to establish invariant before loop body */
    for i in 0..x.len()
        invariant
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
    {
        proof {
            lemma_subrange_extend(x@, i as int);
        }
        
        if x[i] % 3 == 0 {
            y.push(x[i]);
            proof {
                lemma_filter_extend(x@.subrange(0, i as int), x@[i as int], |k:u64| k%3 == 0);
            }
        } else {
            proof {
                lemma_filter_extend(x@.subrange(0, i as int), x@[i as int], |k:u64| k%3 == 0);
            }
        }
    }
}
// </vc-code>

}

fn main() {}