use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn match_strings(s: Seq<char>, p: Seq<char>) -> (b: bool)
  requires s.len() == p.len()
  ensures b == (forall|n: int| 0 <= n < s.len() ==> s[n] == p[n] || p[n] == '?')
// </vc-spec>
// <vc-code>
{
    let length = s.len() as int;
    let mut result: bool = true;
    let mut i: int = 0int;
    while i < length
        invariant
            0 <= i <= length,
            result == (forall |k: int| 0 <= k < i ==> s@[k] == p@[k] || p@[k] == '?'),
    {
        if !(s@[i] == p@[i] || p@[i] == '?') {
            result = false;
        }
        i = i + 1int;
    }
    proof {
        assert(result == (forall |n: int| 0 <= n < s.len() ==> s@[n] == p@[n] || p@[n] == '?'));
    }
    result
}
// </vc-code>

fn main() {
}

}