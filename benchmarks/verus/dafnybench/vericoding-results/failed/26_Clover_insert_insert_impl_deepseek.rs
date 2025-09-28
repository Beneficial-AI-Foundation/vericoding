use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma for vector manipulation
proof fn lemma_vec_insert_preserves_prefix<A>(v:&mut Vec<A>, at: int, new_len: int, i: int)
    requires
        0 <= at <= old(v).len(),
        0 <= new_len - at,
        v =~= old(v).insert(at, new_len - at),
        0 <= i < at,
    ensures
        v@[i] == old(v)@[i],
{
}

proof fn lemma_vec_insert_preserves_suffix<A>(v:&mut Vec<A>, at: int, p: int, new_len: int, i: int)
    requires
        0 <= at <= old(v).len(),
        p == new_len - old(v).len(),
        0 <= p,
        v =~= old(v).insert(at, p),
        at + p <= i < new_len,
    ensures
        v@[i] == old(v)@[i - p],
{
}
// </vc-helpers>

// <vc-spec>
fn insert(line: &mut Vec<char>, l: int, nl: &Vec<char>, p: int, at: int)
    requires 
        0 <= l + p <= old(line).len(),
        0 <= p <= nl.len(),
        0 <= at <= l,
    ensures 
        forall|i: int| (0 <= i < p) ==> line[at + i] == nl[i],
        forall|i: int| (0 <= i < at) ==> line[i] == old(line)[i],
        forall|i: int| (at + p <= i < l + p) ==> line[i] == old(line)[i - p],
// </vc-spec>
// <vc-code>
{
    let original_len = line.len();
    let p_usize: usize = p as usize;
    let at_usize: usize = at as usize;
    let shift_amount: usize = (nl.len() as usize) - p_usize;
    let needed_len: usize = original_len + shift_amount;
    
    // Ensure capacity
    if line.capacity() < needed_len {
        line.reserve(needed_len - line.capacity());
    }
    
    // Extend vector to the new length
    for _ in 0..shift_amount {
        line.push(' ');
    }
    
    // Shift elements to the right
    let mut i: usize = original_len;
    while i > at_usize
        invariant
            at_usize <= i <= original_len,
    {
        i -= 1;
        line[i + shift_amount] = line[i];
    }
    
    // Insert new characters
    for i in 0..p_usize {
        line[at_usize + i] = nl[i];
    }
    
    proof {
        // Prove the postconditions
        let line_seq = line@;
        let old_line_seq = old(line)@;
        let nl_seq = nl@;
        
        assert forall|i: int| (0 <= i < p) implies line_seq[at + i] == nl_seq[i] by {
            assert(0 <= i < p);
        };
        
        assert forall|i: int| (0 <= i < at) implies line_seq[i] == old_line_seq[i] by {
            assert(0 <= i < at);
        };
        
        assert forall|i: int| (at + p <= i < l + p) implies line_seq[i] == old_line_seq[i - p] by {
            assert(at + p <= i < l + p);
        };
    }
}
// </vc-code>

fn main() {
}

}