use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn seq_push_index_preserve<T>(s: Seq<T>, x: T, j: int)
    requires
        0 <= j && j < s.len() as int,
    ensures
        s.push(x)@[j] == s@[j],
{
}

proof fn seq_push_index_last<T>(s: Seq<T>, x: T)
    ensures
        s.push(x)@[s.len() as int] == x,
{
}

fn remove_chars_rec(s1: Seq<char>, s2: Seq<char>, n: nat) -> (v: Seq<char>)
    requires
        n <= s1.len(),
    ensures
        v.len() <= n,
        forall|i: int| 0 <= i && i < v.len() ==> s1.contains(#[trigger] v@[i]) && !s2.contains(#[trigger] v@[i]),
        forall|i: int| 0 <= i && i < n ==> s2.contains(#[trigger] s1@[i]) || v.contains(#[trigger] s1@[i]),
    decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        let m: nat = (n - 1) as nat;
        let mi: int = m as int;
        let rest = remove_chars_rec(s1, s2, m);
        let x = s1@[mi];
        if s2.contains(x) || rest.contains(x) {
            proof {
                assert_forall_by(|i: int| {
                    requires 0 <= i && i < n as int;
                    ensures s2.contains(s1@[i]) || rest.contains(s1@[i]);
                    if i < mi {
                        assert(s2.contains(s1@[i]) || rest.contains(s1@[i]));
                    } else {
                        assert(i == mi);
                        assert(s1@[mi] == x);
                        assert(s2.contains(x) || rest.contains(x));
                    }
                });
            }
            rest
        } else {
            let r2 = rest.push(x);

            // Length bound
            assert(r2.len() == rest.len() + 1);
            assert(rest.len() <= m);
            assert(r2.len() <= n);

            // The new element x is from s1 and not in s2
            assert(0 <= mi && mi < s1.len() as int);
            assert(s1.contains(x));
            assert(!s2.contains(x));

            proof {
                // Elements of r2 are from s1 and not in s2
                assert_forall_by(|i: int| {
                    requires 0 <= i && i < r2.len() as int;
                    ensures s1.contains(r2@[i]) && !s2.contains(r2@[i]);
                    if i < rest.len() as int {
                        assert(seq_push_index_preserve(rest, x, i));
                        assert(r2@[i] == rest@[i]);
                        assert(s1.contains(rest@[i]) && !s2.contains(rest@[i]));
                    } else {
                        assert(i == rest.len() as int);
                        assert(seq_push_index_last(rest, x));
                        assert(r2@[i] == x);
                        assert(s1.contains(x));
                        assert(!s2.contains(x));
                    }
                });

                // Coverage: for all positions < n, either s2 contains or r2 contains
                assert_forall_by(|i: int| {
                    requires 0 <= i && i < n as int;
                    ensures s2.contains(s1@[i]) || r2.contains(s1@[i]);
                    if i < mi {
                        assert(s2.contains(s1@[i]) || rest.contains(s1@[i]));
                        if s2.contains(s1@[i]) {
                            assert(s2.contains(s1@[i]) || r2.contains(s1@[i]));
                        } else {
                            // rest.contains(s1@[i]) holds
                            let j = choose|j: int| 0 <= j && j < rest.len() as int && #[trigger] rest@[j] == s1@[i];
                            assert(0 <= j && j < rest.len() as int);
                            assert(seq_push_index_preserve(rest, x, j));
                            assert(r2@[j] == rest@[j]);
                            assert(r2.contains(s1@[i]));
                        }
                    } else {
                        assert(i == mi);
                        assert(s1@[mi] == x);
                        assert(seq_push_index_last(rest, x));
                        assert(r2@[rest.len() as int] == x);
                        assert(r2.contains(s1@[i]));
                    }
                });
            }

            r2
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_chars(s1: Seq<char>, s2: Seq<char>) -> (v: Seq<char>)
    ensures 
        v.len() <= s1.len(),
        forall|i: int| 0 <= i < v.len() ==> s1.contains(v[i]) && !s2.contains(v[i]),
        forall|i: int| 0 <= i < s1.len() ==> s2.contains(s1[i]) || v.contains(s1[i])
// </vc-spec>
// <vc-code>
{
    let v = remove_chars_rec(s1, s2, s1.len());
    v
}
// </vc-code>

fn main() {
}

}