use vstd::prelude::*;

verus! {

// <vc-helpers>
proof lemma_min_sublist_exists(s: Seq<Seq<int>>)
    requires
        s.len() > 0,
    ensures
        exists|min_sublist: Seq<int>| 
            s.contains(min_sublist) && 
            forall|sublist: Seq<int>| s.contains(sublist) ==> min_sublist.len() <= sublist.len()
{
    let mut min_index: nat = 0;
    let mut min_len: nat = s@[0].len();
    
    let mut i: nat = 1;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            min_index < s.len(),
            s.contains(s@[min_index]),
            s@[min_index].len() == min_len,
            forall|j: nat| j < i ==> s@[j].len() >= min_len
    {
        let current_len = s@[i].len();
        if current_len < min_len {
            min_index = i;
            min_len = current_len;
        }
        i = i + 1;
    }
    
    assert(s.contains(s@[min_index]));
    assert forall|sublist: Seq<int>| s.contains(sublist) implies s@[min_index].len() <= sublist.len() by {
        assert forall|k: nat| k < s.len() implies s@[min_index].len() <= s@[k].len() by {
            assert(k < i);
            assert(s@[k].len() >= min_len);
            assert(s@[min_index].len() == min_len);
        };
    };
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
    proof {
        lemma_min_sublist_exists(s);
    }
    
    let mut min_index: nat = 0;
    let mut min_len: nat = s@[0].len();
    
    let mut i: nat = 1;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            min_index < s.len(),
            s@[min_index].len() == min_len,
            forall|j: nat| j < i ==> s@[j].len() >= min_len
    {
        let current_len = s@[i].len();
        if current_len < min_len {
            min_index = i;
            min_len = current_len;
        }
        i = i + 1;
    }
    
    s@[min_index]
}
// </vc-code>

fn main() {
}

}