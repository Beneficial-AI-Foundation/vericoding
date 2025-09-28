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
proof fn lemma_sqr_sum_rec(n: nat)
    ensures sqr_sum_rec(n as int) == (n as int * (n as int + 1) * (2 * n as int + 1)) / 6
    decreases n
{
    if n == 0 {
        assert(sqr_sum_rec(0) == 0);
        assert((0 * (0 + 1) * (2 * 0 + 1)) / 6 == 0);
    } else {
        lemma_sqr_sum_rec((n - 1) as nat);
        let n_int = n as int;
        assert(sqr_sum_rec(n_int - 1) == ((n_int - 1) * n_int * (2 * n_int - 1)) / 6) by (nonlinear_arith);
        assert(sqr_sum_rec(n_int) == n_int*n_int + sqr_sum_rec(n_int - 1));
        assert(6 * n_int*n_int + (n_int - 1) * n_int * (2 * n_int - 1) ==
               n_int * (6 * n_int + (n_int - 1) * (2 * n_int - 1))) by (nonlinear_arith);
        assert((n_int - 1) * (2 * n_int - 1) == 2 * n_int * n_int - 3 * n_int + 1) by (nonlinear_arith);
        assert(6 * n_int + (2 * n_int * n_int - 3 * n_int + 1) ==
               2 * n_int * n_int + 3 * n_int + 1) by (nonlinear_arith);
        assert(2 * n_int * n_int + 3 * n_int + 1 == (n_int + 1) * (2 * n_int + 1)) by (nonlinear_arith);
        assert(n_int * ((n_int + 1) * (2 * n_int + 1)) == n_int * (n_int + 1) * (2 * n_int + 1)) by (nonlinear_arith);
        assert(n_int*n_int + ((n_int - 1) * n_int * (2 * n_int - 1)) / 6 ==
               (n_int * (n_int + 1) * (2 * n_int + 1)) / 6) by (nonlinear_arith);
    }
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
        invariant
            0 <= i <= n + 1,
            s == sqr_sum_rec(i - 1),
    {
        i = i + 1;
        s = s + ( (i - 1) * (i - 1) );
    }

    assert(i == n + 1);
    assert(s == sqr_sum_rec((n + 1) - 1)); // From loop invariant
    assert(s == sqr_sum_rec(n));

    proof {
        lemma_sqr_sum_rec(n as nat); // To prove that sqr_sum_rec(n) is divisible by 6
    }
    s
}
// </vc-code>

fn main() {
}

}