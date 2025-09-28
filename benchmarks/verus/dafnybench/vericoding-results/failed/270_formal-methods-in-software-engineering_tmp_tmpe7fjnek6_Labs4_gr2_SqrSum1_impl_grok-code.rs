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
#[allow(unused_imports)]
use vstd::prelude::*;

spec fn sum_up_to(k: int) -> int
    recommends k >= -1
{
    if k == -1 {0} else {sqr_sum_rec(k)}
}
// </vc-helpers>

// <vc-spec>
fn sqr_sum1(n: int) -> (s: int)
    requires n >= 0
    ensures s == sqr_sum_rec(n)  // s = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
// </vc-spec>
// <vc-code>
{
    proof {
        assert(sum_up_to(-1) == 0);
    }
    let mut sum: usize = 0;
    let mut i: usize = 0;
    while (i as int) <= n
        invariant 0 <= (i as int) <= n+1, (sum as int) == sum_up_to((i as int) - 1)
        decreases (n - (i as int))
    {
        sum = sum + (i * i);
        i = i + 1;
    }
    assert((i as int) == n+1);
    assert((sum as int) == sum_up_to(n));
    assert(sum_up_to(n) == sqr_sum_rec(n));
    (sum as int)
}
// </vc-code>

fn main() {
}

}