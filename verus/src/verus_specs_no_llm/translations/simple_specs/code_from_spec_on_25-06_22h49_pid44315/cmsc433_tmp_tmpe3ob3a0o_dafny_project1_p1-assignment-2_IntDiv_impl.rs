use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IntDiv(m: int, n: int) -> (d: int, r: int)
    requires
        n > 0
    ensures
        m == n * d + r && 0 <= r < n
{
    if m >= 0 {
        // For non-negative m, use standard division
        let mut q = 0;
        let mut rem = m;
        
        while rem >= n
            invariant
                n > 0,
                rem >= 0,
                m == n * q + rem,
                q >= 0
            decreases rem
        {
            q = q + 1;
            rem = rem - n;
        }
        
        assert(m == n * q + rem && 0 <= rem < n);
        (q, rem)
    } else {
        // For negative m, we need to find q such that m = n * q + r where 0 <= r < n
        
        // First, make m positive by taking absolute value
        let pos_m = -m;  // This is positive since m < 0
        
        // Find quotient and remainder for positive division
        let mut q_pos = 0;
        let mut rem_temp = pos_m;
        
        while rem_temp >= n
            invariant
                n > 0,
                rem_temp >= 0,
                pos_m == n * q_pos + rem_temp,
                q_pos >= 0,
                m < 0,
                pos_m == -m
            decreases rem_temp
        {
            q_pos = q_pos + 1;
            rem_temp = rem_temp - n;
        }
        
        // Now pos_m = n * q_pos + rem_temp, so -pos_m = n * (-q_pos) - rem_temp
        // Since m = -pos_m, we have m = n * (-q_pos) - rem_temp
        
        if rem_temp == 0 {
            // Perfect division: pos_m = n * q_pos, so m = -n * q_pos = n * (-q_pos)
            assert(pos_m == n * q_pos + 0);
            assert(m == -pos_m);
            assert(m == -(n * q_pos));
            assert(m == n * (-q_pos));
            assert(m == n * (-q_pos) + 0);
            assert(0 <= 0 < n);
            (-q_pos, 0)
        } else {
            // We have m = n * (-q_pos) - rem_temp
            // We want m = n * q + r where 0 <= r < n
            // So n * q + r = n * (-q_pos) - rem_temp
            // Rearranging: n * q + r = n * (-q_pos) - rem_temp
            //              n * q + r = n * (-q_pos - 1) + n - rem_temp
            // So q = -q_pos - 1 and r = n - rem_temp
            let q = -q_pos - 1;
            let r = n - rem_temp;
            
            // Verification assertions
            assert(pos_m == n * q_pos + rem_temp);
            assert(rem_temp > 0 && rem_temp < n);  // from loop invariant and termination
            assert(m == -pos_m);
            assert(m == -(n * q_pos + rem_temp));
            assert(m == -n * q_pos - rem_temp);
            
            // Key insight: -n * q_pos - rem_temp = n * (-q_pos - 1) + (n - rem_temp)
            // Because: n * (-q_pos - 1) = -n * q_pos - n
            // So: n * (-q_pos - 1) + (n - rem_temp) = -n * q_pos - n + n - rem_temp = -n * q_pos - rem_temp
            assert(n * (-q_pos - 1) == -n * q_pos - n);
            assert(n * (-q_pos - 1) + (n - rem_temp) == -n * q_pos - n + n - rem_temp);
            assert(n * (-q_pos - 1) + (n - rem_temp) == -n * q_pos - rem_temp);
            assert(m == n * q + r);
            
            // Check remainder bounds
            assert(r == n - rem_temp);
            assert(rem_temp > 0 && rem_temp < n);
            assert(n - n < r && r <= n - 1);
            assert(0 < r && r < n);
            assert(0 <= r < n);
            
            (q, r)
        }
    }
}

}