use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n: usize = s.len();
    for j in 1..n
        invariant forall|k: int, l: int| 0 <= k < l < (j as int) ==> s@[k] != s@[l]
    {
        for i in 0..j {
            if s@[i as int] == s@[j as int] {
                return (true, s@[j as int]);
            }
        }
    }
    return (false, 'a');
}
// </vc-code>

fn main() {}

}