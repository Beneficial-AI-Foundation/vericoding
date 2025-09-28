use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let n: int = s.len() as int;

    let mut min = s[0].len();
    let mut arg = 0;
    let mut j = 0;

    while j < n
        invariant 0 <= j && j <= n
        invariant 0 <= arg && arg < n
        invariant min == s[arg].len()
        invariant forall|k: int| 0 <= k < j ==> min <= #[trigger] s[k].len()
    {
        assert(0 <= j && j < s.len() as int);
        if s[j].len() < min {
            min = s[j].len();
            arg = j;
            assert(0 <= arg && arg < n);
            assert(min == s[arg].len());
        }
        assert(min <= s[j].len());

        assert forall|k: int| 0 <= k < j + 1 ==> min <= #[trigger] s[k].len() by {
            if k < j {
            } else {
                assert(k == j);
                assert(min <= s[j].len());
            }
        }

        j = j + 1;
    }

    assert(j == n);
    assert(forall|k: int| 0 <= k < n ==> min <= #[trigger] s[k].len());
    assert(0 <= arg && arg < s.len());
    assert(min == s[arg].len());
    min as int
}
// </vc-code>

fn main() {
}

}