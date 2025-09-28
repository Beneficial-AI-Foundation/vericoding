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

// </vc-helpers>

// <vc-spec>
fn sqr_sum1(n: int) -> (s: int)
    requires n >= 0
    ensures s == sqr_sum_rec(n)  // s = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let mut sum: int = 0;

    proof {
        reveal(sqr_sum_rec);
        assert(sqr_sum_rec(0) == 0);
    }
    assert(sum == sqr_sum_rec(i));

    while i < n
        invariant 0 <= i && i <= n && sum == sqr_sum_rec(i)
    {
        let old_i = i;
        let old_sum = sum;

        assert(old_i < n);

        proof {
            assert(0 <= old_i);
            reveal(sqr_sum_rec);
            assert(sqr_sum_rec(old_i + 1) == (old_i + 1) * (old_i + 1) + sqr_sum_rec(old_i));
        }

        sum = sum + (old_i + 1) * (old_i + 1);
        i = old_i + 1;

        assert(sum == old_sum + (old_i + 1) * (old_i + 1));
        assert(old_sum == sqr_sum_rec(old_i));
        assert(sqr_sum_rec(i) == (old_i + 1) * (old_i + 1) + sqr_sum_rec(old_i));
        assert(sum == sqr_sum_rec(i));

        assert(i <= n);
    }

    assert(i == n);
    sum
}
// </vc-code>

fn main() {
}

}