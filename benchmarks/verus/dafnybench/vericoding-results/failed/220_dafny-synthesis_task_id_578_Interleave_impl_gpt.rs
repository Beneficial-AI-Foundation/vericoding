use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> (r: Seq<int>)
    requires 
        s1.len() == s2.len() && s2.len() == s3.len(),
    ensures 
        r.len() == 3 * s1.len(),
        forall|i: int| 0 <= i < s1.len() ==> r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i],
// </vc-spec>
// <vc-code>
{
    let n = s1.len();
    assert(s2.len() == n);
    assert(s3.len() == n);
    let len3 = 3 * n;
    assert(0 <= len3);

    let r = Seq::new(len3 as nat, |j: int| {
        if 0 <= j && j < len3 {
            let k = j / 3;
            let m = j % 3;
            if m == 0 {
                proof {
                    assert(j == 3 * k + m);
                    assert(0 <= m && m < 3);
                    assert(0 <= k);
                    assert(3 * k <= j);
                    assert(j < 3 * n);
                    assert(3 * k < 3 * n);
                    assert(k < n);
                }
                s1[k]
            } else if m == 1 {
                proof {
                    assert(j == 3 * k + m);
                    assert(0 <= m && m < 3);
                    assert(0 <= k);
                    assert(3 * k + 1 == j);
                    assert(j < 3 * n);
                    assert(3 * k < 3 * n);
                    assert(k < n);
                }
                s2[k]
            } else {
                proof {
                    assert(m == 2);
                    assert(j == 3 * k + m);
                    assert(0 <= m && m < 3);
                    assert(0 <= k);
                    assert(3 * k + 2 == j);
                    assert(j < 3 * n);
                    assert(3 * k < 3 * n);
                    assert(k < n);
                }
                s3[k]
            }
        } else {
            0
        }
    });

    assert(r.len() == len3 as nat);

    assert(forall|i: int| 0 <= i && i < n ==> r[3 * i] == s1[i]) by {
        assert(forall|i: int|
            0 <= i && i < n ==> {
                let j = 3 * i;
                assert(0 <= j && j < 3 * n);
                assert(j % 3 == 0);
                assert(r[j] == s1[i]);
                true
            }
        );
    };
    assert(forall|i: int| 0 <= i && i < n ==> r[3 * i + 1] == s2[i]) by {
        assert(forall|i: int|
            0 <= i && i < n ==> {
                let j = 3 * i + 1;
                assert(0 <= j && j < 3 * n);
                assert(j % 3 == 1);
                assert(j / 3 == i);
                assert(r[j] == s2[i]);
                true
            }
        );
    };
    assert(forall|i: int| 0 <= i && i < n ==> r[3 * i + 2] == s3[i]) by {
        assert(forall|i: int|
            0 <= i && i < n ==> {
                let j = 3 * i + 2;
                assert(0 <= j && j < 3 * n);
                assert(j % 3 == 2);
                assert(j / 3 == i);
                assert(r[j] == s3[i]);
                true
            }
        );
    };

    r
}
// </vc-code>

fn main() {
}

}