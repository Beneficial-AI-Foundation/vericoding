use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn all_sequences_equal_length_helper(sequences: Seq<Seq<int>>, k: nat) 
    requires
        k <= sequences.len(),
    ensures
        forall |i: nat, j: nat| i < k && j < k ==> sequences[i as int].len() == sequences[j as int].len()
        <==>
        (k == 0 || (forall |i: nat| i < k - 1 ==> sequences[i as int].len() == sequences[(i+1) as int].len() && sequences[0].len() == sequences[(k-1) as int].len()))
{
    if k > 0 {
        all_sequences_equal_length_helper(sequences, (k - 1) as nat);
    }
}

proof fn sequence_equality_transitive(a: int, b: int, c: int)
    ensures
        a == b && b == c ==> a == c
{
}
// </vc-helpers>

// <vc-spec>
fn all_sequences_equal_length(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures result <==> (forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
// </vc-spec>
// <vc-code>
{
    if sequences.len() == 0 {
        return true;
    }
    
    let first_len = sequences[0].len();
    let mut i: int = 0;
    
    while i < sequences.len() as int
        invariant
            0 <= i <= sequences.len() as int,
            forall |j: int| 0 <= j < i ==> sequences[j].len() == first_len,
    {
        if sequences[i].len() != first_len {
            return false;
        }
        i = i + 1;
    }
    
    proof {
        all_sequences_equal_length_helper(sequences, sequences.len() as nat);
    }
    
    true
}
// </vc-code>

fn main() {
}

}