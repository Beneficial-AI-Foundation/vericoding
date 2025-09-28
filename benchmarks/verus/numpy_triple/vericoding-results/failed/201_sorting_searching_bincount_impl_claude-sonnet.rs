// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_val_in_seq(s: Seq<nat>, val: nat, end: int) -> nat
    decreases end
{
    if end <= 0 || end > s.len() {
        0nat
    } else {
        count_val_in_seq(s, val, end - 1) + if s[end - 1] == val { 1nat } else { 0nat }
    }
}

proof fn lemma_count_val_equiv(s: Seq<nat>, val: nat, end: int)
    ensures 0 <= end <= s.len() ==> count_val_in_seq(s, val, end) == s.subrange(0, end).filter(|v: nat| v == val).len()
    decreases end
{
    if 0 <= end && end <= s.len() {
        if end == 0 {
            assert(s.subrange(0, 0) =~= Seq::<nat>::empty());
        } else {
            lemma_count_val_equiv(s, val, end - 1);
            let sub_prev = s.subrange(0, end - 1);
            let sub_curr = s.subrange(0, end);
            assert(sub_curr =~= sub_prev.push(s[end - 1]));
        }
    }
}

proof fn lemma_count_full_seq(s: Seq<nat>, val: nat)
    ensures count_val_in_seq(s, val, s.len() as int) == s.filter(|v: nat| v == val).len()
{
    lemma_count_val_equiv(s, val, s.len() as int);
    assert(s.subrange(0, s.len() as int) =~= s);
}
// </vc-helpers>

// <vc-spec>
spec fn count_occurrences(x: Seq<nat>, val: nat) -> nat {
    x.filter(|v: nat| v == val).len()
}

fn numpy_bincount(x: Vec<u8>, max_val: u8) -> (result: Vec<u8>)
    requires 
        forall|i: int| 0 <= i < x.len() ==> x[i] as nat <= max_val as nat,
    ensures
        result.len() == max_val as nat + 1,
        forall|val: int| 0 <= val <= max_val as int ==> 
            result[val] as nat == count_occurrences(x@.map(|i: int, v: u8| v as nat), val as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to main loop */
    let mut result = Vec::<u8>::with_capacity((max_val as usize) + 1);
    let mut i = 0;
    
    while i <= max_val
        invariant
            result.len() == i as nat,
            forall|val: int| 0 <= val < i as int ==> 
                result[val] as nat == count_occurrences(x@.map(|i: int, v: u8| v as nat), val as nat),
        decreases max_val - i
    {
        let mut count = 0u8;
        let mut j = 0;
        
        while j < x.len()
            invariant
                count as nat == count_val_in_seq(x@.map(|i: int, v: u8| v as nat), i as nat, j as int),
                j <= x.len(),
            decreases x.len() - j
        {
            if x[j] == i {
                count = count + 1;
            }
            j = j + 1;
        }
        
        proof {
            let mapped_seq = x@.map(|i: int, v: u8| v as nat);
            lemma_count_full_seq(mapped_seq, i as nat);
            assert(count as nat == count_occurrences(mapped_seq, i as nat));
        }
        
        result.push(count);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}