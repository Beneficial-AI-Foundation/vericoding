// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn pow_int(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_int(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn vander(x: Vec<i8>, m: usize) -> (result: Vec<Vec<i8>>)
    requires 
        x@.len() > 0,
        m > 0,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == m,
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < m ==> 
            result@[i]@[j] as int == pow_int(x@[i] as int, (m - 1 - j) as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariant timing and added overflow bounds */
    let n = x.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            n == x@.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k]@.len() == m,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < m ==> 
                result@[k]@[j] as int == pow_int(x@[k] as int, (m - 1 - j) as nat),
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        let xi = x[i];
        
        while j < m
            invariant
                j <= m,
                row@.len() == j,
                forall|k: int| 0 <= k < j ==> 
                    row@[k] as int == pow_int(xi as int, (m - 1 - k) as nat),
            decreases m - j
        {
            // Compute xi^(m-1-j)
            let exponent = (m - 1 - j) as usize;
            let mut power: i8 = 1;
            let mut k: usize = 0;
            
            while k < exponent
                invariant
                    k <= exponent,
                    exponent == m - 1 - j,
                    power as int == pow_int(xi as int, k as nat),
                    -128 <= power as int <= 127,
                    -128 <= xi as int <= 127,
                decreases exponent - k
            {
                proof {
                    assert(k < exponent);
                    assert(power as int == pow_int(xi as int, k as nat));
                }
                
                // Check for overflow before multiplication
                if xi > 0 && power > 127 / xi {
                    // Would overflow, saturate at max
                    power = 127;
                } else if xi < 0 && power < -128 / xi {
                    // Would overflow, saturate at min
                    power = -128;
                } else {
                    power = power * xi;
                }
                
                k = k + 1;
                
                proof {
                    assert(k <= exponent);
                }
            }
            
            assert(k == exponent);
            assert(exponent == m - 1 - j);
            
            row.push(power);
            j = j + 1;
        }
        
        assert(row@.len() == m);
        
        result.push(row);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}