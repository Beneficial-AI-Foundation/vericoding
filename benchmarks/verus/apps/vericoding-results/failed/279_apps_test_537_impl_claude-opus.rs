// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 0 && k >= 0 && k + 1 > 0
}

spec fn valid_output(result: Seq<int>, n: int, k: int) -> bool {
    result.len() == 3 &&
    result[0] >= 0 && result[1] >= 0 && result[2] >= 0 &&
    result[1] == result[0] * k &&
    result[0] + result[1] <= n / 2 &&
    result[2] == n - result[0] - result[1]
}

spec fn optimal_diplomas(n: int, k: int) -> int
    recommends valid_input(n, k)
{
    (n / 2) / (k + 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires valid_input(n as int, k as int)
    ensures 
        valid_output(result@.map(|i, x| x as int), n as int, k as int) &&
        result@[0] as int == optimal_diplomas(n as int, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Remove 'as int' from executable code, use i8 arithmetic directly */
    assert(k >= 0);
    assert(n >= 0);
    assert(k as int + 1 > 0);
    
    // Since k >= 0 and k is i8, we know k <= 127
    // But we need k + 1 to not overflow, which is guaranteed since k < 127 or k == 127
    let k_plus_1: i8 = if k == 127 { 127 } else { k + 1 };
    
    // For k == 127, k + 1 would be 128, but we use 127 to avoid overflow
    // This is safe because diplomas will be 0 or very small anyway
    
    let half_n: i8 = n / 2;
    let diplomas: i8 = half_n / k_plus_1;
    
    // Check that diplomas * k won't overflow
    // Since diplomas <= half_n / k_plus_1 and half_n <= n/2 <= 127/2 = 63
    // and diplomas * k <= 63 * 127 which could overflow
    // But actually diplomas <= half_n/(k+1) so diplomas * k <= half_n * k/(k+1) < half_n
    assert(diplomas as int * k as int <= half_n as int);
    
    // Use i8 arithmetic directly, checking for overflow at runtime
    let certificates: i8 = if k == 0 { 0 } else if diplomas <= 127 / k { diplomas * k } else { 0 };
    let commendations: i8 = n - diplomas - certificates;
    
    let mut result = Vec::new();
    result.push(diplomas);
    result.push(certificates);
    result.push(commendations);
    
    assert(result@.len() == 3);
    assert(result@[0] as int == diplomas as int);
    assert(result@[1] as int == certificates as int);
    assert(result@[2] as int == commendations as int);
    assert(result@[1] as int == result@[0] as int * k as int);
    assert(result@[0] as int + result@[1] as int <= n as int / 2);
    assert(result@[2] as int == n as int - result@[0] as int - result@[1] as int);
    
    result
}
// </vc-code>


}

fn main() {}