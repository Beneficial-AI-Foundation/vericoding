use vstd::prelude::*;

verus! {

// <vc-helpers>
fn min(a: int, b: int) -> (r: int)
    ensures
        r <= a,
        r <= b,
        r == a || r == b,
{
    if a < b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_list_length(s: Seq<Seq<int>>) -> (v: int)
    requires
        s.len() > 0,
    ensures
        forall|i: int| 0 <= i < s.len() ==> v <= s[i].len(),
        exists|i: int| 0 <= i < s.len() && v == #[trigger] s[i].len(),
// </vc-spec>
// <vc-code>
{
    let mut smallest_len: int = s[0].len();
    let mut i: int = 1; // Changed 'nat' to 'int'

    let s_len = s.len();

    while i < s_len
        invariant
            0 <= i <= s_len, // Changed invariant to handle i starting from 1
            forall|j: int| 0 <= j < i ==> smallest_len <= s[j].len(),
            exists|k: int| 0 <= k < i && smallest_len == #[trigger] s[k].len(),
    {
        // No change needed for s[i as int].len() as i is already an int.
        smallest_len = min(smallest_len, s[i].len());
        i = i + 1;
    }
    smallest_len
}
// </vc-code>

fn main() {
}

}