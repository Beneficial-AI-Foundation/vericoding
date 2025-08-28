use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_contains_implies_non_empty(s: Seq<Seq<int>>, sublist: Seq<int>)
    requires
        s.contains(sublist),
    ensures
        s.len() > 0,
{
}

fn find_min_length_sublist(s: Seq<Seq<int>>) -> (min_sublist: Seq<int>)
    requires
        s.len() > 0,
    ensures
        s.contains(min_sublist),
        forall |sublist: Seq<int>| s.contains(sublist) ==> min_sublist.len() <= sublist.len(),
{
    let mut min_sublist = s[0];
    let mut i: usize = 1;

    while i < s.len()
        invariant
            0 < i <= s.len(),
            s.contains(min_sublist),
            forall |sublist: Seq<int>| {
                let sublist_index = s.index_of(sublist);
                sublist_index.is_some() && sublist_index.unwrap() < i ==> min_sublist.len() <= sublist.len()
            },
    {
        if s[i].len() < min_sublist.len() {
            min_sublist = s[i];
        }
        i = i + 1;
    }

    min_sublist
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn min_length_sublist(s: Seq<Seq<int>>) -> (min_sublist: Seq<int>)
    requires 
        s.len() > 0,
    ensures 
        s.contains(min_sublist),
        forall |sublist: Seq<int>| s.contains(sublist) ==> min_sublist.len() <= sublist.len(),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn min_length_sublist(s: Seq<Seq<int>>) -> (min_sublist: Seq<int>)
    requires
        s.len() > 0,
    ensures
        s.contains(min_sublist),
        forall |sublist: Seq<int>| s.contains(sublist) ==> min_sublist.len() <= sublist.len(),
{
    find_min_length_sublist(s)
}
// </vc-code>

fn main() {
}

}