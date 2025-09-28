// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1 as int } else { 0 as int })
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_count_rec_step(a: Seq<int>, x: int, i: int)
    requires
        0 <= i < a.len(),
    ensures
        count_rec(a.subrange(0, i + 1), x) == count_rec(a.subrange(0, i), x) + (if a[i] == x { 1int } else { 0int }),
    decreases i
{
    /* helper modified by LLM (iteration 5): Simplified proof using induction on prefix length */
    if i == 0 {
        // Base case: prefix of length 1
        assert(a.subrange(0, 1).len() == 1);
        assert(a.subrange(0, 0).len() == 0);
        assert(count_rec(a.subrange(0, 0), x) == 0);
        assert(a.subrange(0, 1)[0] == a[0]);
        // By definition of count_rec
        assert(count_rec(a.subrange(0, 1), x) == count_rec(a.subrange(0, 1).subrange(1, 1), x) + (if a.subrange(0, 1)[0] == x { 1int } else { 0int }));
        assert(a.subrange(0, 1).subrange(1, 1).len() == 0);
        assert(count_rec(a.subrange(0, 1), x) == 0 + (if a[0] == x { 1int } else { 0int }));
    } else {
        // Inductive case: show count_rec(0..i+1) = count_rec(0..i) + contribution of a[i]
        lemma_count_rec_step(a, x, i - 1);
        
        // Relate prefix[0..i+1] to prefix[0..i]
        assert(a.subrange(0, i + 1) =~= a.subrange(0, i).push(a[i]));
        
        // Apply recursion to the larger prefix
        let prefix = a.subrange(0, i + 1);
        assert(prefix[i] == a[i]);
        
        // Show by induction that adding one element increases count appropriately
        lemma_count_rec_append(a.subrange(0, i), a[i], x);
    }
}

proof fn lemma_count_rec_append(s: Seq<int>, elem: int, x: int)
    ensures
        count_rec(s.push(elem), x) == count_rec(s, x) + (if elem == x { 1int } else { 0int }),
    decreases s.len()
{
    /* helper modified by LLM (iteration 5): Added lemma to prove count_rec property for appending an element */
    if s.len() == 0 {
        assert(s.push(elem).len() == 1);
        assert(count_rec(s.push(elem), x) == count_rec(s.push(elem).subrange(1, 1), x) + (if s.push(elem)[0] == x { 1int } else { 0int }));
        assert(s.push(elem).subrange(1, 1).len() == 0);
        assert(count_rec(s, x) == 0);
    } else {
        let s_with_elem = s.push(elem);
        assert(s_with_elem[0] == s[0]);
        assert(s_with_elem.subrange(1, s_with_elem.len() as int) =~= s.subrange(1, s.len() as int).push(elem));
        
        // Apply recursion
        lemma_count_rec_append(s.subrange(1, s.len() as int), elem, x);
        
        // count_rec(s_with_elem) = count_rec(tail_with_elem) + contribution of s[0]
        // count_rec(s) = count_rec(tail) + contribution of s[0]
        assert(count_rec(s_with_elem, x) == count_rec(s.subrange(1, s.len() as int).push(elem), x) + (if s[0] == x { 1int } else { 0int }));
        assert(count_rec(s, x) == count_rec(s.subrange(1, s.len() as int), x) + (if s[0] == x { 1int } else { 0int }));
    }
}
// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>, x: i8) -> (cnt: i8)
    ensures 
        cnt as int == count_rec(a@.map(|i: int, v: i8| v as int), x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed counting logic and invariant maintenance */
    let mut cnt: i8 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            cnt >= 0,
            cnt as int == count_rec(a@.subrange(0, i as int).map(|j: int, v: i8| v as int), x as int).min(i8::MAX as int),
        decreases a.len() - i
    {
        let old_cnt = cnt;
        let old_i = i;
        
        if a[i] == x && cnt < i8::MAX {
            cnt = cnt + 1;
        }
        
        i = i + 1;
        
        // Prove invariant maintenance
        proof {
            let mapped_seq = a@.map(|j: int, v: i8| v as int);
            let old_prefix = mapped_seq.subrange(0, old_i as int);
            let new_prefix = mapped_seq.subrange(0, i as int);
            
            assert(new_prefix =~= old_prefix.push(mapped_seq[old_i as int]));
            assert(mapped_seq[old_i as int] == a@[old_i as int] as int);
            
            lemma_count_rec_step(mapped_seq, x as int, old_i as int);
            
            let old_count = count_rec(old_prefix, x as int);
            let new_count = count_rec(new_prefix, x as int);
            
            assert(new_count == old_count + (if mapped_seq[old_i as int] == x as int { 1int } else { 0int }));
            
            if a@[old_i as int] == x {
                if old_cnt < i8::MAX {
                    assert(cnt == old_cnt + 1);
                    assert(old_cnt as int == old_count.min(i8::MAX as int));
                    assert(cnt as int == (old_count + 1).min(i8::MAX as int));
                    assert(cnt as int == new_count.min(i8::MAX as int));
                } else {
                    assert(cnt == old_cnt);
                    assert(cnt == i8::MAX);
                    assert(cnt as int == new_count.min(i8::MAX as int));
                }
            } else {
                assert(cnt == old_cnt);
                assert(new_count == old_count);
                assert(cnt as int == new_count.min(i8::MAX as int));
            }
        }
    }
    
    // At loop end, we've processed the entire array
    assert(a@.subrange(0, a.len() as int) =~= a@);
    assert(a@.subrange(0, a.len() as int).map(|j: int, v: i8| v as int) =~= a@.map(|j: int, v: i8| v as int));
    
    // Handle potential overflow in postcondition
    if count_rec(a@.map(|j: int, v: i8| v as int), x as int) <= i8::MAX as int {
        assert(cnt as int == count_rec(a@.map(|j: int, v: i8| v as int), x as int));
    } else {
        assert(cnt == i8::MAX);
        assert(cnt as int == count_rec(a@.map(|j: int, v: i8| v as int), x as int).min(i8::MAX as int));
        // We can't satisfy the postcondition if count exceeds i8::MAX
        // The specification requires exact count, not clamped value
        assert(cnt as int == count_rec(a@.map(|j: int, v: i8| v as int), x as int)); // This will fail if overflow
    }
    
    cnt
}
// </vc-code>


}

fn main() {}