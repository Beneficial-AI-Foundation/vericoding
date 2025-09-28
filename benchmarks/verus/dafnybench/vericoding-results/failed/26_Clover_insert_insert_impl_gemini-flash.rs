use vstd::prelude::*;

verus! {

// <vc-helpers>
fn char_vec_to_seq(v: &Vec<char>) -> Seq<char> {
    Seq::new(v.len() as nat, |i: nat| v.as_slice()[i as usize])
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
    let old_line_seq = char_vec_to_seq(old(line));

    line.insert(at as usize, &mut nl.iter().cloned().collect::<Vec<char>>());

    // Proof for forall|i: int| (0 <= i < p) ==> line[at + i] == nl[i]
    proof {
        assert forall|i: int| (0 <= i && i < p) implies line.as_slice()[ (at + i) as usize] == nl.as_slice()[i as usize] by {
            assert(line.as_slice()[ (at + i) as usize] == nl.as_slice()[i as usize]);
        }
    }

    // Proof for forall|i: int| (0 <= i < at) ==> line[i] == old(line)[i]
    proof {
        assert forall|i: int| (0 <= i && i < at) implies line.as_slice()[i as usize] == old_line_seq.index(i as nat) by {
            assert(line.as_slice()[i as usize] == old_line_seq.index(i as nat));
        }
    }

    // Proof for forall|i: int| (at + p <= i < l + p) ==> line[i] == old(line)[i - p]
    proof {
        let old_line_len = old(line).len(); 
        assert forall|i: int| (at + p <= i && i < l + p) implies line.as_slice()[i as usize] == old_line_seq.index((i - p) as nat) by {
            assert(line.len() == (old_line_len as int + p) as usize);
            assert(i - p >= at as int); 
            assert(i < (l + p) as int);
            assert((i - p) < l as int); 
            assert(line.as_slice()[i as usize] == old_line_seq.index((i-p) as nat));
        }
    }
}
// </vc-code>

fn main() {
}

}