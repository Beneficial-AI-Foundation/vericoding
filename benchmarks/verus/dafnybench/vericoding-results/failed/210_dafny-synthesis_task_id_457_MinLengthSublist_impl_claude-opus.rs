use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn min_so_far_lemma(s: Seq<Seq<int>>, min_so_far: Seq<int>, i: int)
    requires
        0 <= i < s.len(),
        s.contains(min_so_far),
        forall |j: int| 0 <= j < i ==> min_so_far.len() <= s@[j].len(),
    ensures
        if s@[i].len() < min_so_far.len() {
            s.contains(s@[i]) &&
            forall |j: int| 0 <= j <= i ==> s@[i].len() <= s@[j].len()
        } else {
            forall |j: int| 0 <= j <= i ==> min_so_far.len() <= s@[j].len()
        }
{
    assert(s@[i] == s@[i]); // trigger for s.contains
}

proof fn contains_implies_index(s: Seq<Seq<int>>, sublist: Seq<int>)
    requires
        s.contains(sublist),
    ensures
        exists |k: int| 0 <= k < s.len() && s@[k] == sublist,
{
    // This follows from the definition of contains for sequences
}
// </vc-helpers>

// <vc-spec>
fn min_length_sublist(s: Seq<Seq<int>>) -> (min_sublist: Seq<int>)
    requires 
        s.len() > 0,
    ensures 
        s.contains(min_sublist),
        forall |sublist: Seq<int>| s.contains(sublist) ==> min_sublist.len() <= sublist.len(),
// </vc-spec>
// <vc-code>
{
    let ghost s_ghost = s;
    let mut min_sublist = s_ghost@[0];
    let mut i: usize = 1;
    
    while i < s.len() as usize
        invariant
            1 <= i <= s.len(),
            s.contains(min_sublist),
            forall |j: int| 0 <= j < i as int ==> min_sublist.len() <= s_ghost@[j].len(),
    {
        let current_sublist = s_ghost@[i as int];
        if current_sublist.len() < min_sublist.len() {
            proof {
                min_so_far_lemma(s_ghost, min_sublist, i as int);
            }
            min_sublist = current_sublist;
        } else {
            proof {
                min_so_far_lemma(s_ghost, min_sublist, i as int);
            }
        }
        i = i + 1;
    }
    
    assert(i as int == s.len());
    assert(forall |j: int| 0 <= j < s.len() ==> min_sublist.len() <= s_ghost@[j].len());
    
    assert forall |sublist: Seq<int>| s.contains(sublist) implies min_sublist.len() <= sublist.len() by {
        if s.contains(sublist) {
            proof {
                contains_implies_index(s_ghost, sublist);
            }
            let k_witness = choose |k: int| 0 <= k < s.len() && s_ghost@[k] == sublist;
            assert(s_ghost@[k_witness] == sublist);
            assert(min_sublist.len() <= s_ghost@[k_witness].len());
            assert(min_sublist.len() <= sublist.len());
        }
    }
    
    min_sublist
}
// </vc-code>

fn main() {
}

}