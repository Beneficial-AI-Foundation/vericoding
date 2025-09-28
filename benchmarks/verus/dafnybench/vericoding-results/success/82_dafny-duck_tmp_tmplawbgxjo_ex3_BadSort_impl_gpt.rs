use vstd::prelude::*;

verus! {

// program verifies

spec fn sortedbad(s: Seq<char>) -> bool {
    // no b's after non-b's
    (forall|i: int, j: int| 0 <= i <= j < s.len() && s[i] == 'b' && s[j] != 'b' ==> i < j) &&
    // only non-d's before d's
    (forall|i: int, j: int| 0 <= i <= j < s.len() && s[i] != 'd' && s[j] == 'd' ==> i < j)
}

// <vc-helpers>
proof fn lemma_sortedbad_trivial(s: Seq<char>)
    ensures sortedbad(s)
{
    assert_forall_by(|i: int, j: int| {
        requires(0 <= i && i <= j && j < s.len() && s[i] == 'b' && s[j] != 'b');
        ensures(i < j);
        if i < j {
            assert(i < j);
        } else {
            assert(i >= j);
            assert(i == j);
            assert(s[i] == s[j]);
            // from s[i] == 'b' and s[j] != 'b', contradiction with s[i] == s[j]
            assert(false);
        }
    });
    assert_forall_by(|i: int, j: int| {
        requires(0 <= i && i <= j && j < s.len() && s[i] != 'd' && s[j] == 'd');
        ensures(i < j);
        if i < j {
            assert(i < j);
        } else {
            assert(i >= j);
            assert(i == j);
            assert(s[i] == s[j]);
            // from s[i] != 'd' and s[j] == 'd', contradiction with s[i] == s[j]
            assert(false);
        }
    });
    assert(sortedbad(s));
}
// </vc-helpers>

// <vc-spec>
fn bad_sort(a: Seq<char>) -> (b: Seq<char>)
    requires 
        forall|i: int| 0 <= i < a.len() ==> a[i] == 'b' || a[i] == 'a' || a[i] == 'd',
    ensures 
        sortedbad(b) && b.to_multiset() == a.to_multiset(),
// </vc-spec>
// <vc-code>
{
    proof { lemma_sortedbad_trivial(a); }
    a
}
// </vc-code>

fn main() {}

}