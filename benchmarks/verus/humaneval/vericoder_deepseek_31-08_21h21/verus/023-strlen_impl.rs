use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn seq_len<T>(s: Seq<T>) -> nat
    decreases s.len(),
{
    s.len()
}

proof fn proof_seqs_equal<T>(s1: Seq<T>, s2: Seq<T>) 
    requires 
        s1.len() == s2.len(),
        forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i],
    ensures 
        s1 =~= s2,
{
    reveal_with_fuel(seq_len, 2);
}

ghost fn push_ghost_char(ghost_chars: Seq<char>, ch: char) -> (updated: Seq<char>)
    ensures
        updated.len() == ghost_chars.len() + 1,
        forall|i: int| 0 <= i < ghost_chars.len() ==> updated[i] == ghost_chars[i],
        updated[ghost_chars.len()] == ch,
{
    ghost_chars.push(ch)
}
// </vc-helpers>

// <vc-spec>
fn strlen(string: &Vec<char>) -> (length: usize)
    // post-conditions-start
    ensures
        length == string.len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut length: usize = 0;
    let mut index: usize = 0;
    let ghost mut ghost_chars = Seq::<char>::empty();
    
    while index < string.len()
        invariant
            length == index,
            index <= string.len(),
            ghost_chars.len() == index,
            forall|i: int| 0 <= i < index ==> ghost_chars[i] == string@[i],
    {
        proof {
            ghost_chars = push_ghost_char(ghost_chars, string[index]);
        }
        length = length + 1;
        index = index + 1;
    }
    
    proof {
        proof_seqs_equal(ghost_chars, string@);
    }
    
    assert(ghost_chars =~= string@);
    length
}
// </vc-code>

fn main() {}
}