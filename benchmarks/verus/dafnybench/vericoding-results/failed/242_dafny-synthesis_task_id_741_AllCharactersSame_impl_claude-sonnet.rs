use vstd::prelude::*;

verus! {

// <vc-helpers>
fn lemma_empty_seq_all_same(s: Seq<u8>)
    requires s.len() == 0
    ensures forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@[i] == s@[j]
{
}

fn lemma_single_element_all_same(s: Seq<u8>)
    requires s.len() == 1
    ensures forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@[i] == s@[j]
{
}

fn lemma_all_same_check(s: Seq<u8>, first: u8) -> (result: bool)
    requires 
        s.len() > 0,
        first == s@[0]
    ensures 
        result <==> (forall|i: int| 0 <= i < s.len() ==> s@[i] == first),
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@[i] == s@[j]),
        !result ==> (exists|i: int| 0 <= i < s.len() && s@[i] != first)
{
    if forall|i: int| 0 <= i < s.len() ==> s@[i] == first {
        assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@[i] == s@[j]) by {
            assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s@[i] == first && s@[j] == first);
        }
        true
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
fn all_characters_same(s: Seq<u8>) -> (result: bool)
    ensures
        result ==> (forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]),
        !result ==> (s.len() > 1) && (exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s[i] != s[j])
// </vc-spec>
// <vc-code>
{
    if s.len() <= 1nat {
        proof {
            if s.len() == 0 {
                lemma_empty_seq_all_same(s);
            } else {
                lemma_single_element_all_same(s);
            }
        }
        return true;
    }
    
    let first = s@[0];
    
    let mut i: usize = 1;
    while i < s.len() as usize
        invariant
            0 < i <= s.len(),
            forall|k: int| 0 <= k < i ==> s@[k] == first
    {
        if s@[i as int] != first {
            assert(s@[0] == first);
            assert(s@[i as int] != first);
            assert(0 != i);
            assert(exists|x: int, y: int| 0 <= x < s.len() && 0 <= y < s.len() && x != y && s@[x] != s@[y]) by {
                assert(s@[0] != s@[i as int] && 0 != i && 0 <= 0 < s.len() && 0 <= i < s.len());
            }
            return false;
        }
        i = i + 1;
    }
    
    assert(forall|k: int| 0 <= k < s.len() ==> s@[k] == first);
    assert(forall|x: int, y: int| 0 <= x < s.len() && 0 <= y < s.len() ==> s@[x] == s@[y]) by {
        assert(forall|x: int, y: int| 0 <= x < s.len() && 0 <= y < s.len() ==> s@[x] == first && s@[y] == first);
    }
    
    true
}
// </vc-code>

fn main() {
}

}