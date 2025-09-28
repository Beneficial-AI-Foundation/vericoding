// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(a: Seq<i32>, key: i32) -> nat {
    a.filter(|x: i32| x == key).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed filter property assertions using sequence axioms */
proof fn lemma_filter_properties(a: Seq<i32>, key: i32, i: int)
    requires 0 <= i < a.len()
    ensures
        a.subrange(0, i + 1) =~= a.subrange(0, i).push(a[i]),
        (a[i] == key) ==> (a.subrange(0, i + 1).filter(|x: i32| x == key).len() == a.subrange(0, i).filter(|x: i32| x == key).len() + 1),
        (a[i] != key) ==> (a.subrange(0, i + 1).filter(|x: i32| x == key).len() == a.subrange(0, i).filter(|x: i32| x == key).len()),
{
    assert(a.subrange(0, i + 1) =~= a.subrange(0, i).push(a[i]));
    
    if a[i] == key {
        let filtered_prefix = a.subrange(0, i).filter(|x: i32| x == key);
        let filtered_extended = a.subrange(0, i + 1).filter(|x: i32| x == key);
        
        assert(filtered_extended.len() == filtered_prefix.len() + 1);
    } else {
        let filtered_prefix = a.subrange(0, i).filter(|x: i32| x == key);
        let filtered_extended = a.subrange(0, i + 1).filter(|x: i32| x == key);
        
        assert(filtered_extended.len() == filtered_prefix.len());
    }
}
// </vc-helpers>

// <vc-spec>
fn only_once(a: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> count_occurrences(a@, key) == 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed assertion to use length instead of sequence equality */
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count as nat == count_occurrences(a@.subrange(0, i as int), key),
            count <= 1,
        decreases a.len() - i
    {
        if a[i] == key {
            proof {
                lemma_filter_properties(a@, key, i as int);
                assert(count_occurrences(a@.subrange(0, i as int + 1), key) == count_occurrences(a@.subrange(0, i as int), key) + 1);
            }
            count = count + 1;
            if count > 1 {
                return false;
            }
        } else {
            proof {
                lemma_filter_properties(a@, key, i as int);
                assert(count_occurrences(a@.subrange(0, i as int + 1), key) == count_occurrences(a@.subrange(0, i as int), key));
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(a@.subrange(0, i as int) =~= a@);
        assert(count as nat == count_occurrences(a@, key));
    }
    
    count == 1
}
// </vc-code>

}
fn main() {}