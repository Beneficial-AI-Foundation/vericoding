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
// Helper lemmas (kept minimal; main proof strategy uses int-based loop variables)
proof fn u32_sub_as_int(x: u32, y: u32)
    requires x >= y
    ensures (x - y) as int == x as int - y as int
{
    // Trivial by cast semantics when no wrap-around.
}

proof fn u32_add_one_as_int(x: u32)
    requires x < std::u32::MAX
    ensures (x + 1) as int == x as int + 1
{
    // Trivial when addition does not wrap.
}

proof fn u32_as_int_le_max(x: u32)
    ensures x as int <= std::u32::MAX as int
{
    // Trivial: casting a u32 to int yields a value at most u32::MAX
}
// </vc-helpers>

// <vc-spec>
fn DivMod1(a: u32, b: u32) -> (result: (u32, u32))
    requires b > 0 && a >= 0
    ensures a == b * result.0 + result.1 && 0 <= result.1 < b
// </vc-spec>
// <vc-code>
{
    // Use integer (mathematical) loop variables to simplify arithmetic reasoning.
    let mut qi: int = 0;
    let mut ri: int = a as int;

    while ri >= b as int
        invariant a as int == b as int * qi + ri;
        invariant 0 <= ri && ri <= a as int;
        decreases ri;
    {
        ri = ri - b as int;
        qi = qi + 1;
    }

    // Now safely cast back to u32 after proving bounds.
    assert(qi >= 0);
    assert(qi <= a as int);
    proof { u32_as_int_le_max(a); }
    assert(a as int <= std::u32::MAX as int);
    // From qi <= a and a <= MAX we get qi <= MAX
    proof {
        u32_as_int_le_max(a);
        assert(qi <= std::u32::MAX as int);
    }
    assert(ri >= 0);
    assert(ri <= std::u32::MAX as int);

    let q: u32 = qi as u32;
    let r: u32 = ri as u32;

    (q, r)
}
// </vc-code>

fn main() {
}

}