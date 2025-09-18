// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemmas for gcd properties and fixed gcd_impl */
proof fn lemma_gcd_properties(a: int, b: int)
    ensures
        gcd(a, b) == gcd(int_abs(a), int_abs(b)),
        a == 0 && b == 0 ==> gcd(a, b) == 0,
        a != 0 && b == 0 ==> gcd(a, b) == int_abs(a),
        a == 0 && b != 0 ==> gcd(a, b) == int_abs(b),
        gcd(a, b) == gcd(b, a),
    decreases int_abs(a) + int_abs(b),
{}

proof fn lemma_gcd_divisibility(a: int, b: int, g: int)
    requires g == gcd(a, b),
    ensures
        a == 0 && b == 0 ==> g == 0,
        a != 0 || b != 0 ==> g > 0,
        a != 0 || b != 0 ==> a % g == 0 && b % g == 0,
        forall|d: int| (a % d == 0 && b % d == 0) ==> g % d == 0,
    decreases int_abs(a) + int_abs(b),
{}

fn gcd_impl(a: i32, b: i32) -> (result: i32)
    ensures
        result >= 0,
        result as int == gcd(a as int, b as int),
{
    if a == 0 && b == 0 {
        proof { lemma_gcd_properties(a as int, b as int); }
        return 0;
    }
    
    let mut x = if a < 0 { -a } else { a };
    let mut y = if b < 0 { -b } else { b };
    
    if a == i32::MIN {
        x = 0;
        y = if b == i32::MIN { 0 } else { y };
    }
    if b == i32::MIN {
        y = 0;
        x = if a == i32::MIN { 0 } else { x };
    }
    
    while y != 0
        invariant
            x >= 0,
            y >= 0,
            gcd(x as int, y as int) == gcd(int_abs(a as int), int_abs(b as int)),
            gcd(int_abs(a as int), int_abs(b as int)) == gcd(a as int, b as int),
        decreases y,
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    
    proof { 
        lemma_gcd_properties(a as int, b as int);
        assert(y == 0);
        assert(gcd(x as int, 0) == int_abs(x as int));
        assert(x >= 0);
        assert(gcd(x as int, 0) == x as int);
    }
    
    x
}
// </vc-helpers>

// <vc-spec>
spec fn gcd(a: int, b: int) -> int 
decreases int_abs(a) + int_abs(b), 

{
    if a == 0 && b == 0 {
        0
    } else if a == 0 {
        int_abs(b)
    } else if b == 0 {
        int_abs(a)
    } else if int_abs(a) >= int_abs(b) {
        gcd(int_abs(b), int_abs(a) % int_abs(b))
    } else {
        gcd(int_abs(a), int_abs(b) % int_abs(a))
    }
}


spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn numpy_gcd(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == gcd(#[trigger] x1[i] as int, #[trigger]  x2[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> gcd(#[trigger] x1[i] as int, x2[i] as int) == gcd(#[trigger] int_abs(x1[i] as int), #[trigger] int_abs(x2[i] as int)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == 0 && x2[i] == 0) ==> #[trigger] result[i] == 0,
        forall|i: int| 0 <= i < result.len() ==> (x1[i] != 0 && x2[i] == 0) ==> #[trigger] result[i] as int == int_abs(x1[i] as int),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == 0 && x2[i] != 0) ==> #[trigger] result[i] as int == int_abs(x2[i] as int),
        forall|i: int| 0 <= i < result.len() ==> (result[i] as int) % (x1[i] as int) == 0 && (result[i] as int) % (x2[i] as int) == 0,
        forall|i: int, d: int| 0 <= i < result.len() 
            ==>  (d % (x1[i] as int) == 0 && d % (x2[i] as int) == 0) ==> #[trigger] (d % (result[i] as int)) == 0,
        forall|i: int| 0 <= i < result.len() ==> gcd(x2[i] as int, #[trigger] x1[i] as int) == gcd(x1[i] as int, #[trigger] x2[i] as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariants and postcondition proofs */
    let mut result: Vec<i32> = Vec::new();
    let n = x1.len();
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            i <= x1.len(),
            i <= x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> j < x1.len(),
            forall|j: int| 0 <= j < i ==> j < x2.len(),
            forall|j: int| 0 <= j < i ==> result[j] as int == gcd(x1[j] as int, x2[j] as int),
            forall|j: int| 0 <= j < i ==> result[j] >= 0,
        decreases n - i,
    {
        assert(i < n);
        assert(i < x1.len());
        assert(i < x2.len());
        
        let a = x1[i];
        let b = x2[i];
        
        let g = gcd_impl(a, b);
        
        proof {
            lemma_gcd_properties(a as int, b as int);
            lemma_gcd_divisibility(a as int, b as int, g as int);
            assert(g as int == gcd(a as int, b as int));
            assert(g >= 0);
        }
        
        result.push(g);
        
        assert(result.len() == i + 1);
        assert(result[i as int] == g);
        assert(g as int == gcd(a as int, b as int));
        assert(g as int == gcd(x1[i as int] as int, x2[i as int] as int));
        
        i = i + 1;
    }
    
    proof {
        assert(i == n);
        assert(result.len() == n);
        assert(result.len() == x1.len());
        assert(forall|j: int| 0 <= j < result.len() ==> result[j] as int == gcd(x1[j] as int, x2[j] as int));
        assert(forall|j: int| 0 <= j < result.len() ==> result[j] >= 0);
        
        assert forall|j: int| 0 <= j < result.len() implies {
            lemma_gcd_properties(x1[j] as int, x2[j] as int);
            lemma_gcd_divisibility(x1[j] as int, x2[j] as int, result[j] as int);
            (result[j] as int) % (x1[j] as int) == 0 && (result[j] as int) % (x2[j] as int) == 0
        };
        
        assert forall|j: int, d: int| 0 <= j < result.len() implies {
            lemma_gcd_divisibility(x1[j] as int, x2[j] as int, result[j] as int);
            ((d % (x1[j] as int) == 0 && d % (x2[j] as int) == 0) ==> (d % (result[j] as int)) == 0)
        };
    }
    
    result
}
// </vc-code>

}
fn main() {}