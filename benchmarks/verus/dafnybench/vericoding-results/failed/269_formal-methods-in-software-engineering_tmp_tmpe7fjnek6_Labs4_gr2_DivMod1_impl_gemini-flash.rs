use vstd::prelude::*;

verus! {

/*
Verus include 2 limbaje:
    * un limbaj pentru specificare 
        MSFOL (ce am discutat până acum)
        adnotări care să ajute în procesul de verificare
    * un limbaj pentru scris programe
*/

// Exemplu de program



/*
    triple Hoare (| P |) S (| Q |) 
*/

// varianta assume-assert

// varianta requires-ensures


/*
regula pentru while
*/

// varianta cu assert
/*
*/

// varianta cu invariant

//specificarea sumei de patrate
spec fn SqrSumRec(n: int) -> int
    decreases n when n >= 0
{
    if n <= 0 { 0 } else { n*n + SqrSumRec(n-1) }
}
/*
*/

// verificarea programului pentru suma de patrate


// SqrSumRec(n) = 0^2 + 1^2 + 2^2 + ... + n^2 == n(n+1)(2n+1)/6
proof fn L1(n: int)
    requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
    decreases n
{
    if n == 0 {
        // Base case holds automatically
    } else {
        L1(n-1);
        // Inductive step would require additional arithmetic reasoning
    }
}

/*
spec fn SqrSumBy6(n: int) -> int
{
    n * (n + 1) * (2 * n + 1) 
}

proof fn L(n: int) // it takes a while
    decreases n
    requires n >= 0
    ensures  SqrSumBy6(n) == 6 * SqrSumRec(n)
{
    if n == 0 {
    } else {
        assert(n > 0);
        L(n-1);
        assert(SqrSumBy6(n-1) == n*(n-1)*(2*n - 1));
        assert(SqrSumBy6(n-1) == 6*SqrSumRec(n-1));
        assert(6*SqrSumRec(n-1) == n*(n-1)*(2*n - 1));
        // Sequential assertions replacing calc chains
        assert(n*((n-1)*(2*n - 1)) == n*(2*n*(n-1) - n + 1));
        assert(n*(2*n*(n-1) - n + 1) == n*(2*n*n - 3*n + 1));
        
        assert(2*n*n + n == (2*n + 1)*n);
        
        assert((2*n + 1)*n + (2*n + 1) == (2*n + 1)*(n+1));
        
        // Additional algebraic steps would be needed here
    }
}

*/

// <vc-helpers>
proof fn lemma_div_mod_property(a: u32, b: u32, q: u32, r: u32)
    requires a == b * q + r && r >= b
    ensures (a == b * (q + 1) + (r - b))
{
    assert(b * (q + 1) + (r - b) == b * q + b + r - b) by(nonlinear_arith) ;
    assert(b * q + b + r - b == b * q + r) by(nonlinear_arith) ;
    assert(b * q + r == a) by(nonlinear_arith) ;
}

proof fn L1(n: int)
    requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
    decreases n
{
    if n == 0 {
        assert(SqrSumRec(0) == 0);
        assert(0 * (0 + 1) * (2 * 0 + 1) / 6 == 0);
    } else {
        L1(n-1);
        // S_n = S_{n-1} + n^2
        // S_n = (n-1)n(2n-1)/6 + n^2
        // S_n = (n(2n^2 - 3n + 1) + 6n^2)/6
        // S_n = (n(2n^2 - 3n + 1 + 6n))/6
        // S_n = (n(2n^2 + 3n + 1))/6
        // S_n = (n(n+1)(2n+1))/6
        assert(SqrSumRec(n) == SqrSumRec(n-1) + n*n);
        assert(SqrSumRec(n-1) == (n-1)*n*(2*n - 1)/6) by(nonlinear_arith);
        assert((n-1)*n*(2*n - 1)/6 + n*n == ( (n-1)*n*(2*n - 1) + 6*n*n ) / 6) by(nonlinear_arith);
        assert(( (n-1)*n*(2*n - 1) + 6*n*n ) / 6 == ( n*( (n-1)*(2*n - 1) + 6*n ) ) / 6) by(nonlinear_arith);
        assert((n-1)*(2*n - 1) + 6*n == (2*n*n - 3*n + 1) + 6*n) by(nonlinear_arith);
        assert((2*n*n - 3*n + 1) + 6*n == 2*n*n + 3*n + 1) by(nonlinear_arith);
        assert(2*n*n + 3*n + 1 == (n+1)*(2*n+1)) by(nonlinear_arith);
        assert(n*(n+1)*(2*n+1)/6 == (n*(2*n*n + 3*n + 1))/6) by(nonlinear_arith);

        assert(SqrSumRec(n) == n*(n+1)*(2*n + 1)/6);
    }
}
// </vc-helpers>

// <vc-spec>
fn DivMod1(a: u32, b: u32) -> (result: (u32, u32))
    requires b > 0 && a >= 0
    ensures a == b * result.0 + result.1 && 0 <= result.1 < b
// </vc-spec>
// <vc-code>
{
    let mut q: u32 = 0;
    let mut r: u32 = a;

    while r >= b
        invariant
            b > 0,
            a == b * q + r,
            r >= 0,
            //r is going down by b, which is > 0, so it will eventually terminate
            decreases r
    {
        proof {
            lemma_div_mod_property(a, b, q, r);
        }
        r = r - b;
        q = q + 1;
    }
    (q, r)
}
// </vc-code>

fn main() {
}

}