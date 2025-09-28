use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn torneo(valores: &Vec<int>, i: usize, j: usize, k: usize) -> (res: (usize, usize))
    requires 
        valores.len() >= 20 && valores.len() < 50,
        i < valores.len() && j < valores.len() && k < valores.len(),
        i != j && j != k && k != i,
    ensures 
        exists|p: usize, q: usize, r: usize| 
            (p == i || p == j || p == k) &&
            (q == i || q == j || q == k) &&  
            (r == i || r == j || r == k) &&
            p != q && q != r && p != r &&
            valores[p as int] >= valores[q as int] && 
            valores[q as int] >= valores[r as int] &&
            res.0 == p && 
            res.1 == q, // Q
// </vc-spec>
// <vc-code>
{
    // Compare the three values and determine the order
    let val_i = valores[i];
    let val_j = valores[j];
    let val_k = valores[k];
    
    // Find first and second place
    let result = if val_i >= val_j && val_i >= val_k {
        // i is first place
        if val_j >= val_k {
            // Order: i >= j >= k
            (i, j)
        } else {
            // Order: i >= k > j
            (i, k)
        }
    } else if val_j >= val_i && val_j >= val_k {
        // j is first place
        if val_i >= val_k {
            // Order: j >= i >= k
            (j, i)
        } else {
            // Order: j >= k > i
            (j, k)
        }
    } else {
        // k is first place (since one of them must be >= the others)
        if val_i >= val_j {
            // Order: k >= i >= j
            (k, i)
        } else {
            // Order: k >= j > i
            (k, j)
        }
    };
    
    // Prove the postcondition
    proof {
        let p = result.0;
        let q = result.1;
        
        // Determine r based on p and q
        let r = if p == i && q == j { k }
               else if p == i && q == k { j }
               else if p == j && q == i { k }
               else if p == j && q == k { i }
               else if p == k && q == i { j }
               else { i }; // p == k && q == j
        
        // Assert the postcondition properties
        assert(p == i || p == j || p == k);
        assert(q == i || q == j || q == k);
        assert(r == i || r == j || r == k);
        assert(p != q);
        assert(q != r);
        assert(p != r);
        assert(valores[p as int] >= valores[q as int]);
        assert(valores[q as int] >= valores[r as int]);
    }
    
    result
}
// </vc-code>

fn main() {}

}