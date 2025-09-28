use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
fn is_sublist(sub: Seq<int>, main: Seq<int>) -> (result: bool)
    ensures
        result == exists|i: int, j: int| 0 <= i <= main.len() - sub.len() && j == i + sub.len() && sub =~= #[trigger] main.subrange(i, j)
// </vc-spec>
// <vc-code>
{
    let n: nat = main.len();
    let m: nat = sub.len();
    if m > n {
        return false;
    }
    let n_i: int = n as int;
    let m_i: int = m as int;
    let limit: int = n_i - m_i;
    let mut i: int = 0;
    while i <= limit
        invariant { 0 <= i && i <= limit + 1 }
        invariant { forall |t: int| 0 <= t && t < i ==> !(sub =~= #[trigger] main.subrange(t, t + m_i)) }
    {
        if sub =~= #[trigger] main.subrange(i, i + m_i) {
            let ii: int = i;
            let jj: int = ii + m_i;
            proof {
                assert(0 <= ii);
                assert(ii <= n_i - m_i);
                assert(jj == ii + m_i);
                assert(sub =~= #[trigger] main.subrange(ii, jj));
            }
            return true;
        }
        i = i + 1;
    }
    proof {
        // from loop exit and invariant we have i == limit + 1
        assert(!(i <= limit));
        assert(i <= limit + 1);
        assert(i == limit + 1);
        let I: int = i;
        assert(I == limit + 1);
        // use the invariant to show there cannot be any valid starting index
        assert(forall |t: int| 0 <= t && t < I ==> !(sub =~= #[trigger] main.subrange(t, t + m_i)));
        assert(!exists |ii: int, jj: int|
            0 <= ii && ii <= n_i - m_i && jj == ii + m_i && sub =~= #[trigger] main.subrange(ii, jj)
        );
    }
    false
}
// </vc-code>

fn main() {
}

}