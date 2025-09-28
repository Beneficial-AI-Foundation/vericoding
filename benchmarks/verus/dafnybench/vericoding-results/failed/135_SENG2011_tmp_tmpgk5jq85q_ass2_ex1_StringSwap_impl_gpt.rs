use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn string_swap(s: Seq<char>, i: nat, j: nat) -> (t: Seq<char>)
    requires 
        i >= 0 && j >= 0 && s.len() >= 0,
        s.len() > 0 ==> i < s.len() && j < s.len(),
    ensures 
        s.to_multiset() == t.to_multiset(),
        s.len() == t.len(),
        s.len() > 0 ==> forall|k: nat| k != i && k != j && k < s.len() ==> t[k as int] == s[k as int],
        s.len() > 0 ==> t[i as int] == s[j as int] && t[j as int] == s[i as int],
        s.len() == 0 ==> t == s,
// </vc-spec>
// <vc-code>
{
    if s.len() == 0 {
        s
    } else {
        if i == j {
            s
        } else {
            assert(i < s.len() && j < s.len());
            let ghost si = s[i as int];
            let ghost sj = s[j as int];
            let ghost t1 = s.update(i as int, sj);
            assert(t1.len() == s.len());
            assert(t1[j as int] == s[j as int]);
            let ghost t2 = t1.update(j as int, si);
            assert(t2.len() == s.len());
            assert(t2[i as int] == sj);
            assert(t2[j as int] == si);

            assert forall |k: nat|
                k != i && k != j && k < s.len()
                ==> #[trigger] t2[k as int] == s[k as int]
            by {
                if k != i && k != j && k < s.len() {
                    assert(k < t1.len());
                    assert(k < t2.len());
                    assert(t2[k as int] == t1[k as int]);
                    assert(t1[k as int] == s[k as int]);
                }
            }

            proof {
                assert(t1.to_multiset() == s.to_multiset().remove(s[i as int]).insert(sj));
                assert(t2.to_multiset() == t1.to_multiset().remove(t1[j as int]).insert(si));
                assert(t1[j as int] == s[j as int]);

                let m0 = s.to_multiset();
                let m1 = m0.remove(si);
                let m2 = m1.insert(sj);
                let m3 = m2.remove(sj);
                let m4 = m3.insert(si);

                assert(t2.to_multiset() == m2.remove(sj).insert(si));
                assert(m3 == m1);
                assert(m4 == m0);
                assert(t2.to_multiset() == m4);
                assert(t2.to_multiset() == s.to_multiset());
            }

            t2
        }
    }
}
// </vc-code>

// string == Seq<char>
//give se2011 ass2 ex1.dfy

fn main() {}

}