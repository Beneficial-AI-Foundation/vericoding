// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define prefix_eq over sequence views capturing prefix-wise equality */
open spec fn prefix_eq(a1: Seq<f32>, a2: Seq<f32>, k: int) -> bool {
    0 <= k <= a1.len() &&
    a1.len() == a2.len() &&
    forall|j: int| 0 <= j < k ==> a1[j] == a2[j]
}

/* helper modified by LLM (iteration 5): lemma to move between k and k+1 and extract equality at index i */
proof fn prefix_eq_push(a1: Seq<f32>, a2: Seq<f32>, i: int)
    requires a1.len() == a2.len(),
             0 <= i < a1.len(),
    ensures (prefix_eq(a1, a2, i) && a1[i] == a2[i]) ==> prefix_eq(a1, a2, i + 1),
            prefix_eq(a1, a2, i + 1) ==> prefix_eq(a1, a2, i),
            prefix_eq(a1, a2, i + 1) ==> a1[i] == a2[i]
{
    assert((prefix_eq(a1, a2, i) && a1[i] == a2[i]) ==> prefix_eq(a1, a2, i + 1)) by {
        if prefix_eq(a1, a2, i) && a1[i] == a2[i] {
            assert(0 <= i + 1 && i + 1 <= a1.len());
            assert(forall|j: int| 0 <= j < i + 1 ==> a1[j] == a2[j]) by {
                assert forall|j: int| 0 <= j < i + 1 implies a1[j] == a2[j] by {
                    if j < i {
                        assert(0 <= j && j < i);
                    } else {
                        assert(j == i);
                        assert(a1[j] == a2[j]);
                    }
                }
            };
            assert(prefix_eq(a1, a2, i + 1));
        }
    };

    assert(prefix_eq(a1, a2, i + 1) ==> prefix_eq(a1, a2, i)) by {
        if prefix_eq(a1, a2, i + 1) {
            assert(0 <= i && i <= a1.len());
            assert(forall|j: int| 0 <= j < i ==> a1[j] == a2[j]) by {
                assert forall|j: int| 0 <= j < i implies a1[j] == a2[j] by {
                    assert(0 <= j && j < i + 1);
                }
            };
            assert(prefix_eq(a1, a2, i));
        }
    };

    assert(prefix_eq(a1, a2, i + 1) ==> a1[i] == a2[i]) by {
        if prefix_eq(a1, a2, i + 1) {
            assert(0 <= i && i < i + 1);
            assert(a1[i] == a2[i]);
        }
    };
}

/* helper modified by LLM (iteration 5): full-length prefix equivalence iff element-wise forall equivalence */
proof fn prefix_eq_len_iff_forall(a1: Seq<f32>, a2: Seq<f32>)
    requires a1.len() == a2.len(),
    ensures prefix_eq(a1, a2, a1.len()) == (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i])
{
    assert(prefix_eq(a1, a2, a1.len()) ==> (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i])) by {
        if prefix_eq(a1, a2, a1.len()) {
            assert forall|i: int| 0 <= i < a1.len() implies a1[i] == a2[i] by {
                assert(0 <= i && i < a1.len());
            }
        }
    };
    assert((forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i]) ==> prefix_eq(a1, a2, a1.len())) by {
        if (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i]) {
            assert(0 <= a1.len() && a1.len() <= a1.len());
            assert(forall|j: int| 0 <= j < a1.len() ==> a1[j] == a2[j]) by {
                assert forall|j: int| 0 <= j < a1.len() implies a1[j] == a2[j] by { }
            };
            assert(prefix_eq(a1, a2, a1.len()));
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn array_equiv(a1: Vec<f32>, a2: Vec<f32>) -> (result: bool)
    requires a1.len() == a2.len(),
    ensures result == (forall|i: int| 0 <= i < a1.len() ==> a1[i] == a2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed a parsing error by splitting a combined assert, and tightened proofs bridging Vec and Seq equality */
    let n = a1.len();
    let mut i: usize = 0;
    let mut ok: bool = true;

    proof {
        assert(a1@.len() == n as int);
        assert(a2@.len() == n as int);
        assert(a1@.len() == a2@.len());
        assert(prefix_eq(a1@, a2@, 0));
    }

    while i < n
        invariant 0 <= i as int && i as int <= n as int
            && a1.len() == n
            && a2.len() == n
            && a1@.len() == n as int
            && a2@.len() == n as int
            && ok == prefix_eq(a1@, a2@, i as int)
        decreases (n as int) - (i as int)
    {
        proof {
            assert(a1@.len() == a2@.len());
            assert(0 <= i as int);
            assert(i as int < a1@.len());
            prefix_eq_push(a1@, a2@, i as int);
        }

        let next_ok = ok && (a1[i] == a2[i]);

        proof {
            let ip: int = i as int;
            assert(0 <= ip);
            assert(ip < a1@.len());
            assert(ok == prefix_eq(a1@, a2@, ip));

            // next_ok ==> prefix_eq(..., ip + 1)
            assert(next_ok ==> prefix_eq(a1@, a2@, ip + 1)) by {
                if next_ok {
                    assert(ok);
                    assert(prefix_eq(a1@, a2@, ip));
                    // Bridge Vec equality at i to Seq equality at ip
                    assert(a1@[ip] == a1[i]);
                    assert(a2@[ip] == a2[i]);
                    assert(a1@[ip] == a2@[ip]);
                    prefix_eq_push(a1@, a2@, ip);
                    assert(prefix_eq(a1@, a2@, ip + 1));
                }
            };

            // prefix_eq(..., ip + 1) ==> next_ok
            assert(prefix_eq(a1@, a2@, ip + 1) ==> next_ok) by {
                if prefix_eq(a1@, a2@, ip + 1) {
                    // From k+1 prefix, we can step back to k and extract equality at ip
                    prefix_eq_push(a1@, a2@, ip);
                    assert(prefix_eq(a1@, a2@, ip));
                    assert(ok == prefix_eq(a1@, a2@, ip));
                    assert(ok);
                    assert(a1@[ip] == a2@[ip]);
                    // Bridge back to Vec indexing
                    assert(a1@[ip] == a1[i]);
                    assert(a2@[ip] == a2[i]);
                }
            };
        }

        ok = next_ok;
        i = i + 1;
    }

    proof {
        assert(i as int == n as int);
        assert(a1@.len() == n as int);
        assert(ok == prefix_eq(a1@, a2@, i as int));
        assert(ok == prefix_eq(a1@, a2@, a1@.len()));
        prefix_eq_len_iff_forall(a1@, a2@);
        let A = (forall|j: int| 0 <= j < a1@.len() ==> a1@[j] == a2@[j]);
        let B = (forall|j: int| 0 <= j < a1.len() ==> a1[j] == a2[j]);
        // A ==> B
        assert(A ==> B) by {
            if A {
                assert forall|j: int| 0 <= j < a1.len() implies a1[j] == a2[j] by {
                    assert(a1@.len() == a1.len() as int);
                    assert(0 <= j && j < a1.len());
                    assert(0 <= j && j < a1@.len());
                    assert(a1@[j] == a2@[j]);
                    assert(a1@[j] == a1[j]);
                    assert(a2@[j] == a2[j]);
                }
            }
        };
        // B ==> A
        assert(B ==> A) by {
            if B {
                assert forall|j: int| 0 <= j < a1@.len() implies a1@[j] == a2@[j] by {
                    assert(a1@.len() == a1.len() as int);
                    assert(0 <= j && j < a1@.len());
                    assert(0 <= j && j < a1.len());
                    assert(a1[j] == a2[j]);
                    assert(a1@[j] == a1[j]);
                    assert(a2@[j] == a2[j]);
                }
            }
        };
        // Conclude ok == B using the above and ok == A
        assert(ok ==> B) by {
            if ok {
                assert(ok == A);
                assert(A);
            }
        };
        assert(B ==> ok) by {
            if B {
                assert(A);
                assert(ok == A);
            }
        };
        assert(ok == B);
    }

    ok
}
// </vc-code>

}
fn main() {}