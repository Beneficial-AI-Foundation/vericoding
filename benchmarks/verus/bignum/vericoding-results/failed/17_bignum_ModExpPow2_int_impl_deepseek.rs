use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type errors in Exp_int parameter types and return type */
proof fn mod_exp_pow2_invariant(x: nat, k: nat, n: nat, z: nat) 
    requires 0 < z, k <= n
    ensures Exp_int(x, Exp_int(2, k)) % z == Exp_int(Exp_int(x, Exp_int(2, k)) % z, Exp_int(2, (n - k) as nat)) % z
    decreases n - k
{
    if k < n {
        mod_exp_pow2_invariant(x, (k + 1) as nat, n, z);
        
        let base = Exp_int(x, Exp_int(2, k)) % z;
        let next_power = base * base % z;
        
        assert(Exp_int(x, Exp_int(2, k + 1)) == Exp_int(x, Exp_int(2, k)) * Exp_int(x, Exp_int(2, k)));
        assert(Exp_int(x, Exp_int(2, k + 1)) % z == next_power);
        assert(Exp_int(base, 2) == base * base);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_int(x: u64, y: u64, n: u64, z: u64) -> (res: u64)
  requires z > 0u64,
   (y as nat) == Exp_int(2, n as nat)
  ensures (res as nat) == Exp_int(x as nat, y as nat) % (z as nat)
  decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type conversion and expression evaluation */
{
    if n == 0 {
        assert(y == 0u64 || y == 1u64);
        let result = 1u64 % z;
        proof {
            assert(Exp_int(x as nat, y as nat) == 1);
        }
        return result;
    }
    
    let mut k = 0u64;
    let mut current = x % z;
    let mut result = 1u64;
    
    while k < n
        invariant
            k <= n,
            current as nat == Exp_int(x as nat, Exp_int(2, k as nat)) % (z as nat),
            result as nat == Exp_int(x as nat, (y >> (n - k)) as nat) % (z as nat),
        decreases n - k
    {
        proof {
            mod_exp_pow2_invariant(x as nat, k as nat, n as nat, z as nat);
        }
        
        if (y >> (n - k - 1)) & 1u64 == 1u64 {
            result = (result * current) % z;
        }
        
        current = (current * current) % z;
        k = k + 1u64;
    }
    
    proof {
        assert((y as nat) == Exp_int(2, n as nat));
        assert(y >> 0 == y);
    }
    
    result
}
// </vc-code>

fn main() {}
}


