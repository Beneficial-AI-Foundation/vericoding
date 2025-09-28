use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn subranges_equal_up_to<A>(s1: Seq<A>, s2: Seq<A>, k: nat)
    requires
        k <= s1.len(),
        k <= s2.len(),
        forall|j: int| 0 <= j && j < k as int ==> s1[j] == s2[j]
    ensures
        s1.subrange(0, k as int) == s2.subrange(0, k as int)
{
    let s1p = s1.subrange(0, k as int);
    let s2p = s2.subrange(0, k as int);

    assert(s1p.len() == k);
    assert(s2p.len() == k);

    assert(forall|j: int| 0 <= j && j < k as int ==> #[trigger] s1p[j] == #[trigger] s2p[j]) by {
        assert(s1p.len() == k);
        assert(s2p.len() == k);
        assert forall |j:int| 0 <= j && j < k as int implies s1p[j] == s2p[j] by {
            assert(0 <= j && j < s1p.len() as int);
            assert(0 <= j && j < s2p.len() as int);
            assert(s1p[j] == s1[j]);
            assert(s2p[j] == s2[j]);
        }
    }
    assert(s1p == s2p);
}

fn lcp_len<A>(s1: Seq<A>, s2: Seq<A>) -> (k: nat)
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 || s2.len() == 0 {
        0
    } else if s1[0] == s2[0] {
        let s1p = s1.subrange(1, s1.len() as int);
        let s2p = s2.subrange(1, s2.len() as int);
        lcp_len(s1p, s2p) + 1
    } else {
        0
    }
}

proof fn lcp_lemmas<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        lcp_len::<A>(s1, s2) <= s1.len(),
        lcp_len::<A>(s1, s2) <= s2.len(),
        forall |j:int| 0 <= j && j < lcp_len::<A>(s1, s2) as int ==> s1[j] == s2[j],
        lcp_len::<A>(s1, s2) == s1.len() || lcp_len::<A>(s1, s2) == s2.len() ||
            (s1[lcp_len::<A>(s1, s2) as int] != s2[lcp_len::<A>(s1, s2) as int])
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 || s2.len() == 0 {
        assert(lcp_len::<A>(s1, s2) == 0);
    } else {
        if s1[0] == s2[0] {
            let s1p = s1.subrange(1, s1.len() as int);
            let s2p = s2.subrange(1, s2.len() as int);
            lcp_lemmas::<A>(s1p, s2p);
            let kp = lcp_len::<A>(s1p, s2p);
            let k = lcp_len::<A>(s1, s2);
            assert(k == kp + 1);

            assert(kp <= s1p.len());
            assert(kp <= s2p.len());

            assert((s1p.len() as int) == s1.len() as int - 1);
            assert((s2p.len() as int) == s2.len() as int - 1);
            assert((s1p.len() + 1) as int == s1.len() as int);
            assert((s2p.len() + 1) as int == s2.len() as int);
            assert(s1p.len() + 1 == s1.len());
            assert(s2p.len() + 1 == s2.len());

            assert(k <= s1.len()) by { assert(kp + 1 <= s1p.len() + 1); }
            assert(k <= s2.len()) by { assert(kp + 1 <= s2p.len() + 1); }

            assert forall |j:int| 0 <= j && j < k as int implies #[trigger] s1[j] == #[trigger] s2[j] by {
                if j == 0 {
                    assert(s1[0] == s2[0]);
                } else {
                    let jj = j - 1;
                    assert(0 <= j);
                    assert(0 <= jj);
                    assert(j < k as int);
                    assert(k as int == kp as int + 1);
                    assert(jj < kp as int);
                    assert(0 <= jj && jj < s1p.len() as int);
                    assert(0 <= jj && jj < s2p.len() as int);

                    assert(s1p[jj] == s2p[jj]);
                    assert(s1p[jj] == s1[1 + jj]);
                    assert(s2p[jj] == s2[1 + jj]);
                    assert(1 + jj == j);
                    assert(s1[j] == s2[j]);
                }
            }

            if kp == s1p.len() {
                assert(k == s1.len());
            } else if kp == s2p.len() {
                assert(k == s2.len());
            } else {
                let kpi = kp as int;
                assert(s1p[kpi] != s2p[kpi]);

                assert(0 <= kpi && kpi < s1p.len() as int);
                assert(0 <= kpi && kpi < s2p.len() as int);

                assert(k as int == kp as int + 1);
                assert(1 + kpi == k as int);

                assert(s1p[kpi] == s1[1 + kpi]);
                assert(s2p[kpi] == s2[1 + kpi]);

                assert(s1[k as int] == s1p[kpi]);
                assert(s2[k as int] == s2p[kpi]);

                assert(s1[k as int] != s2[k as int]);
            }
        } else {
            assert(lcp_len::<A>(s1, s2) == 0);
            assert(lcp_len::<A>(s1, s2) <= s1.len());
            assert(lcp_len::<A>(s1, s2) <= s2.len());
            assert forall |j:int| 0 <= j && j < lcp_len::<A>(s1, s2) as int implies #[trigger] s1[j] == #[trigger] s2[j] by { }
            assert(s1[lcp_len::<A>(s1, s2) as int] != s2[lcp_len::<A>(s1, s2) as int]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn longest_common_prefix(str1: Seq<char>, str2: Seq<char>) -> (prefix: Seq<char>)
    ensures 
        prefix.len() <= str1.len() && prefix == str1.subrange(0, prefix.len() as int) &&
        prefix.len() <= str2.len() && prefix == str2.subrange(0, prefix.len() as int),
        prefix.len() == str1.len() || prefix.len() == str2.len() || 
        (str1[prefix.len() as int] != str2[prefix.len() as int])
// </vc-spec>
// <vc-code>
{
    let k = lcp_len::<char>(str1, str2);
    lcp_lemmas::<char>(str1, str2);
    let prefix0 = str1.subrange(0, k as int);
    proof {
        subranges_equal_up_to::<char>(str1, str2, k);
        assert(prefix0 == str2.subrange(0, k as int));
    }
    prefix0
}
// </vc-code>

fn main() {
}

}