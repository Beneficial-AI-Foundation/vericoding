use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::seq::*;

proof fn lemma_seq_contains_implies_index_exists<T>(s: Seq<T>, val: T)
    requires
        s.contains(val),
    ensures
        exists|i: int| 0 <= i < s.len() && s[i] == val,
{
    let index = choose|i: int| 0 <= i < s.len() && s[i] == val;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures 
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 && 
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j]))
// </vc-spec>
// </vc-spec>

// <vc-code>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 &&
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j])),
{
    let len = s@.len();
    let mut i: usize = 0;

    while i < len
        invariant
            0 <= i <= len,
            forall|k: int, l: int| 0 <= k < l < i ==> s@[k] != s@[l],
    {
        let mut j: usize = i + 1;
        while j < len
            invariant
                0 <= i < j <= len,
                forall|k: int, l: int| 0 <= k < l < i ==> s@[k] != s@[l],
                forall|k: int| i <= k < j ==> s@[k] != s@[i],
        {
            if s@[i] == s@[j] {
                return (true, s@[i]);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    (false, ' ')
}
// </vc-code>

fn main() {}

}