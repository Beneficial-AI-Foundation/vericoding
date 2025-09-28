use vstd::prelude::*;

verus! {

/*
Verus includes 2 languages:
    * a language for specification 
        MSFOL (what we've discussed so far)
        annotations to help in the verification process
    * a language for writing programs
*/

// Example program

/*
    triple Hoare (| P |) S (| Q |) 
*/

// assume-assert variant

// requires-ensures variant

/*
rule for while
*/

// assert variant
/*
*/

// invariant variant

//specification of sum of squares
spec fn sqr_sum_rec(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n == 0 { 0 } else { n*n + sqr_sum_rec(n-1) }
}
/*

*/

// verification of the program for sum of squares

// SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
proof fn l1(n: int)
    requires n >= 0
    ensures sqr_sum_rec(n) == n*(n+1)*(2*n + 1)/6
    decreases n
{
    //OK
}

/*
spec fn sqr_sum_by_6(n: int) -> int
{
    n * (n + 1) * (2 * n + 1) 
}

proof fn l(n: int) // it takes a while
    requires n >= 0
    ensures sqr_sum_by_6(n) == 6 * sqr_sum_rec(n)
    decreases n
{
    if n == 0 {}
    else {
        assert(n > 0);
        l(n-1);
        assert(sqr_sum_by_6(n-1) == n*(n-1)*(2*n - 1));
        assert(sqr_sum_by_6(n-1) == 6*sqr_sum_rec(n-1));
        assert(6*sqr_sum_rec(n-1) == n*(n-1)*(2*n - 1));
        calc! (==)
        n*((n-1)*(2*n - 1)); {
            n*(2*n*(n-1) - n + 1); {
                n*(2*n*n - 3*n + 1); {
                    n*(2*n*n - 3*n + 1);
                }
            }
        }
        calc! (==)
        2*n*n + n; {
            (2*n + 1)*n;
        }
        calc! (==)
        (2*n + 1)*n + (2*n + 1); {
            (2*n + 1)*(n+1);
        }
        calc! (==)
        n*((n-1)*(2*n - 1)) + 6*n*n; {
            n*(2*n*(n-1) - n + 1) + 6*n*n; {
                n*(2*n*(n-1) - n + 1) + 6*n*n; {
                    n*(2*n*n - 3*n + 1) + 6*n*n; {
                        n*(2*n*n - 3*n + 1 + 6*n); {
                            n*(2*n*n + 6*n - 3*n + 1); {
                                n*(2*n*n + 3*n + 1); {
                                    n*(2*n*n + n + (2*n + 1)); {
                                        n*((2*n + 1)*n + (2*n + 1)); {
                                            n*((2*n + 1)*(n+1));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

*/

// <vc-helpers>
proof fn sqr_sum_unfold(k: int)
    requires k > 0
    ensures sqr_sum_rec(k) == k*k + sqr_sum_rec(k-1)
    decreases k
{
    // By the definition of sqr_sum_rec
}

proof fn sqr_sum_zero()
    ensures sqr_sum_rec(0) == 0
{
    // By the definition of sqr_sum_rec
}
// </vc-helpers>

// <vc-spec>
fn sqr_sum1(n: int) -> (s: int)
    requires n >= 0
    ensures s == sqr_sum_rec(n)  // s = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let mut s: int = 0;
    while i <= n
        invariant 0 <= i && i <= n + 1;
        invariant (i == 0 ==> s == 0);
        invariant (i > 0 ==> s == sqr_sum_rec(i-1));
        decreases (n - i + 1);
    {
        let old_i = i;
        let old_s = s;
        // body executes only when old_i <= n
        s = old_s + old_i * old_i;
        i = old_i + 1;

        // Prove the invariant holds for the updated i and s
        if old_i == 0 {
            // s was 0, added 0, so s == 0, and sqr_sum_rec(0) == 0
            proof {
                sqr_sum_zero();
            }
            assert(old_s == 0);
            assert(s == 0);
            // i == old_i + 1, so s == sqr_sum_rec(i-1)
            assert(s == sqr_sum_rec(old_i));
        } else {
            // old_i > 0: by invariant before the update, old_s == sqr_sum_rec(old_i-1)
            assert(old_i > 0);
            assert(old_s == sqr_sum_rec(old_i - 1));
            proof {
                // use unfolding lemma
                sqr_sum_unfold(old_i);
            }
            // From unfolding lemma and previous invariant we get:
            // new s == old_s + old_i*old_i == sqr_sum_rec(old_i-1) + old_i*old_i == sqr_sum_rec(old_i)
            assert(s == sqr_sum_rec(old_i));
        }
    }

    // After the loop, i > n and invariant gives i <= n+1, so i == n+1
    assert(!(i <= n));
    assert(i <= n + 1);
    assert(i == n + 1);

    // i > 0 holds because n >= 0 so n+1 > 0; use invariant to conclude s == sqr_sum_rec(i-1) == sqr_sum_rec(n)
    assert(i > 0);
    assert(s == sqr_sum_rec(i - 1));
    s
}
// </vc-code>

fn main() {
}

}