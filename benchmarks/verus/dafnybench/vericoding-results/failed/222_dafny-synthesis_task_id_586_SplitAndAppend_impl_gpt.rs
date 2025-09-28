use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn mod_eq_self_if_lt(a: nat, m: nat)
    requires
        m > 0,
        a < m,
    ensures
        a % m == a
{
    assert(0 <= a);
    assert(a < m);
    assert(a % m == a);
}

proof fn mod_eq_minus_m_if_between(a: nat, m: nat)
    requires
        m > 0,
        m <= a < 2 * m,
    ensures
        a % m == a - m
{
    assert(a == m + (a - m));
    assert(0 <= a - m);
    assert(a - m < m);
    assert((m + (a - m)) % m == a - m);
    assert(a % m == a - m);
}
// </vc-helpers>

// <vc-spec>
fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
// </vc-spec>
// <vc-code>
{
    proof {
        let L: int = l.len() as int;
        assert(0 <= L);

        assert(0 <= n && n < L);

        let a = l.subrange(n, L);
        let b = l.subrange(0, n);
        let rr = a + b;

        assert(a.len() as int == L - n);
        assert(b.len() as int == n);
        assert(rr.len() == a.len() + b.len());
        assert(rr.len() as int == L);
        assert(rr.len() == l.len());

        assert(forall|i: int|
            0 <= i < l.len() ==> #[trigger] rr[i] == l[((i + n) as nat % l.len()) as int]
        ) by {
            assert forall|i: int|
                0 <= i < l.len() ==> #[trigger] rr[i] == l[((i + n) as nat % l.len()) as int]
            by {
                if 0 <= i && i < l.len() {
                    assert(L == l.len() as int);
                    assert(0 <= n && n < L);
                    assert(a.len() as int == L - n);
                    assert(rr.len() == l.len());

                    if i < L - n {
                        assert(0 <= i);
                        assert(i < a.len() as int);
                        assert(rr.len() as int == L);
                        assert(i < rr.len() as int);

                        assert(rr[i] == a[i]);
                        assert(a[i] == l[n + i]);

                        assert(0 <= i + n);
                        assert(i + n < L);

                        let x: nat = (i + n) as nat;
                        let m: nat = l.len();
                        assert(m > 0);
                        assert(x < m);

                        mod_eq_self_if_lt(x, m);
                        assert(((i + n) as nat % l.len()) as int == i + n);
                    } else {
                        assert(i >= L - n);
                        let j: int = i - (L - n);
                        assert(j == i + n - L);
                        assert(0 <= j);
                        assert(i < L);
                        assert(j < n);

                        assert(rr.len() as int == L);
                        assert(i < rr.len() as int);

                        assert(rr[i] == b[j]);
                        assert(b[j] == l[j]);

                        assert(0 <= i + n);
                        let x: nat = (i + n) as nat;
                        let m: nat = l.len();
                        assert(m > 0);

                        assert(i + n >= L);
                        assert(x >= m);

                        assert(i < L && n < L);
                        assert(i + n < 2 * L);
                        assert(x < 2 * m);

                        mod_eq_minus_m_if_between(x, m);
                        assert(((i + n) as nat % l.len()) as int == ((i + n) as nat - l.len()) as int);
                        assert(((i + n) as nat - l.len()) as int == i + n - L);
                        assert(l[((i + n) as nat % l.len()) as int] == l[j]);
                    }
                }
            }
        }

        return rr;
    }
}
// </vc-code>

fn main() {
}

}