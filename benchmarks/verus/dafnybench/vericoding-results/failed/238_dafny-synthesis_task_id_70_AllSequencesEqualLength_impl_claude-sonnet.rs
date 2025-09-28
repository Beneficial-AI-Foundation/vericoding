use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_all_equal_via_first<T>(sequences: Seq<Seq<T>>)
    requires sequences.len() > 0
    ensures (forall |k: int| 0 <= k < sequences.len() ==> sequences[k].len() == sequences[0].len()) 
        <==> (forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
{
    if forall |k: int| 0 <= k < sequences.len() ==> sequences[k].len() == sequences[0].len() {
        assert(forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len()) by {
            assert(forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> {
                sequences[i].len() == sequences[0].len() && sequences[j].len() == sequences[0].len()
            });
        }
    }
    
    if forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len() {
        assert(forall |k: int| 0 <= k < sequences.len() ==> sequences[k].len() == sequences[0].len()) by {
            assert(forall |k: int| 0 <= k < sequences.len() ==> {
                sequences[k].len() == sequences[0].len()
            });
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn all_sequences_equal_length(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures result <==> (forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
// </vc-spec>
// <vc-code>
{
    if sequences.len() <= 1 {
        proof {
            assert(forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len()) by {
                if sequences.len() == 0 {
                    assert(forall |i: int, j: int| 0 <= i < 0 && 0 <= j < 0 ==> sequences[i].len() == sequences[j].len());
                } else {
                    assert(sequences.len() == 1);
                    assert(forall |i: int, j: int| 0 <= i < 1 && 0 <= j < 1 ==> i == 0 && j == 0);
                }
            }
        }
        true
    } else {
        let first_len = sequences[0].len();
        let mut all_equal = true;
        let mut k: usize = 1;
        
        while k < sequences.len()
            invariant 
                0 < sequences.len(),
                1 <= k <= sequences.len(),
                all_equal <==> (forall |idx: int| 0 <= idx < k ==> sequences[idx].len() == first_len)
        {
            if sequences[k as int].len() != first_len {
                all_equal = false;
                proof {
                    assert(!(forall |idx: int| 0 <= idx < k + 1 ==> sequences[idx].len() == first_len));
                }
                break;
            }
            k = k + 1;
        }
        
        proof {
            lemma_all_equal_via_first(sequences);
            if all_equal {
                assert(forall |idx: int| 0 <= idx < sequences.len() ==> sequences[idx].len() == first_len);
            } else {
                assert(exists |idx: int| 0 <= idx < sequences.len() && sequences[idx].len() != first_len);
                assert(!(forall |idx: int| 0 <= idx < sequences.len() ==> sequences[idx].len() == first_len));
            }
        }
        
        all_equal
    }
}
// </vc-code>

fn main() {
}

}