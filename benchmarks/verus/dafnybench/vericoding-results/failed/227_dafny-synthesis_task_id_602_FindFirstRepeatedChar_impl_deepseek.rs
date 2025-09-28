use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn has_duplicate_up_to(seq: Seq<char>, idx: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < idx && seq[i] == seq[j]
}

spec fn find_first_dup_char(seq: Seq<char>) -> (bool, char) {
    if exists|i: int, j: int| 0 <= i < j < seq.len() && seq[i] == seq[j] {
        let min_j = choose|j: int| 0 <= j < seq.len() && exists|i: int| 0 <= i < j && seq[i] == seq[j];
        let min_i = choose|i: int| 0 <= i < min_j && seq[i] == seq[min_j];
        (true, seq[min_i])
    } else {
        (false, 'a')
    }
}

proof fn lemma_find_first_dup_char_correct(seq: Seq<char>)
    ensures
        (find_first_dup_char(seq).0 ==> exists|i: int, j: int| 0 <= i < j < seq.len() && seq[i] == seq[j] && seq[i] == find_first_dup_char(seq).1 && 
            (forall|k: int, l: int| 0 <= k < l < j && seq[k] == seq[l] ==> k >= i)) &&
        (!find_first_dup_char(seq).0 ==> (forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j]))
{
    if exists|i: int, j: int| 0 <= i < j < seq.len() && seq[i] == seq[j] {
        let j = choose|j: int| 0 <= j < seq.len() && exists|i: int| 0 <= i < j && seq[i] == seq[j];
        let i = choose|i: int| 0 <= i < j && seq[i] == seq[j];
        
        assert forall|k: int, l: int| 0 <= k < l < j && seq[k] == seq[l] implies k >= i by {
            assert(!(k < i));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures 
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 && 
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j]))
// </vc-spec>
// <vc-code>
{
    let seq = s@;
    let mut seen_chars: Vec<char> = Vec::new();
    let mut result = (false, 'a');
    
    proof {
        lemma_find_first_dup_char_correct(seq);
    }
    
    let mut j: usize = 0;
    let len = s.len();
    
    while j < len
        invariant
            0 <= j <= len,
            seen_chars@.len() == j,
            forall|i: int| 0 <= i < j ==> seen_chars@[i] == seq[i],
            !has_duplicate_up_to(seq, j),
            result == (false, 'a')
    {
        let current_char = seq[j];
        
        let mut i: usize = 0;
        let mut found = false;
        
        while i < j
            invariant
                0 <= i <= j,
                !found ==> forall|k: int| 0 <= k < i ==> seen_chars@[k] != current_char,
                found ==> exists|k: int| 0 <= k < i && seen_chars@[k] == current_char
        {
            proof {
                assert(seen_chars@[i] == seq[i]);
            }
            if seen_chars[i] == current_char {
                found = true;
                break;
            }
            i += 1;
        }
        
        if found {
            result = (true, current_char);
            break;
        }
        
        seen_chars.push(current_char);
        j += 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}