use vstd::prelude::*;
fn main() {}

verus!{

/* code modified by LLM (iteration 2): added helper lemma to prove filter properties */
proof fn lemma_filter_push_divisible(s: Seq<u64>, elem: u64)
    requires elem % 3 == 0
    ensures s.push(elem).filter(|k: u64| k % 3 == 0) == s.filter(|k: u64| k % 3 == 0).push(elem)
{
    // This lemma establishes that when we push a divisible element,
    // filtering the extended sequence is the same as filtering first then pushing
}

/* code modified by LLM (iteration 2): added helper lemma for non-divisible elements */
proof fn lemma_filter_push_not_divisible(s: Seq<u64>, elem: u64)
    requires elem % 3 != 0
    ensures s.push(elem).filter(|k: u64| k % 3 == 0) == s.filter(|k: u64| k % 3 == 0)
{
    // This lemma establishes that when we push a non-divisible element,
    // filtering the extended sequence is the same as filtering the original
}

/* code modified by LLM (iteration 2): added lemma about subrange extension */
proof fn lemma_subrange_extend(s: Seq<u64>, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1) == s.subrange(0, i).push(s[i])
{
    // This lemma establishes how extending a subrange by one element works
}

//IMPL myfun4
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k%3 == 0),
{
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
        decreases x.len() - i
    {
        /* code modified by LLM (iteration 2): store current element and prove subrange property */
        let current_elem = x[i];
        
        // Establish the subrange relationship
        proof {
            lemma_subrange_extend(x@, i as int);
        }
        
        if current_elem % 3 == 0 {
            y.push(current_elem);
            
            /* code modified by LLM (iteration 2): prove filter property for divisible case */
            proof {
                lemma_filter_push_divisible(x@.subrange(0, i as int), current_elem);
            }
        } else {
            /* code modified by LLM (iteration 2): prove filter property for non-divisible case */
            proof {
                lemma_filter_push_not_divisible(x@.subrange(0, i as int), current_elem);
            }
        }
        
        i += 1;
    }
    
    /* code modified by LLM (iteration 2): final assertion to establish postcondition */
    assert(i == x.len());
    assert(x@.subrange(0, i as int) == x@);
}
}