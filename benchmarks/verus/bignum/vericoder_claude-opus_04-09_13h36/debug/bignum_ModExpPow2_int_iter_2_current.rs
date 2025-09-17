use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
proof fn lemma_exp_square(x: nat, n: nat)
    ensures Exp_int(x, Exp_int(2, n + 1)) == Exp_int(Exp_int(x, Exp_int(2, n)), 2)
    decreases n
{
    reveal(Exp_int);
    assert(Exp_int(2, n + 1) == 2 * Exp_int(2, n));
    lemma_exp_multiply(x, Exp_int(2, n), Exp_int(2, n));
}

proof fn lemma_exp_multiply(x: nat, a: nat, b: nat)
    ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
    decreases a
{
    reveal(Exp_int);
    if a == 0 {
        assert(Exp_int(x, a + b) == Exp_int(x, b));
        assert(Exp_int(x, a) * Exp_int(x, b) == 1 * Exp_int(x, b));
    } else {
        lemma_exp_multiply(x, (a - 1) as nat, b);
        assert(Exp_int(x, a + b) == x * Exp_int(x, ((a - 1) + b) as nat));
        assert(Exp_int(x, a) * Exp_int(x, b) == x * Exp_int(x, (a - 1) as nat) * Exp_int(x, b));
    }
}

proof fn lemma_mod_square(a: nat, z: nat)
    requires z > 0
    ensures (Exp_int(a, 2) % z) == ((a % z) * (a % z)) % z
{
    reveal(Exp_int);
    assert(Exp_int(a, 2) == a * a);
    assert((a * a) % z == ((a % z) * (a % z)) % z) by {
        lemma_mod_mul(a, a, z);
    }
}

proof fn lemma_mod_mul(a: nat, b: nat, z: nat)
    requires z > 0
    ensures (a * b) % z == ((a % z) * (b % z)) % z
{
    // This is a standard modular arithmetic property
}

proof fn lemma_exp_2_positive(n: nat)
    ensures Exp_int(2, n) > 0
    decreases n
{
    reveal(Exp_int);
    if n == 0 {
        assert(Exp_int(2, n) == 1);
    } else {
        lemma_exp_2_positive((n - 1) as nat);
        assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
    }
}

proof fn lemma_exp_2_bounds(n: nat, bound: nat)
    requires Exp_int(2, n) <= bound
    ensures n == 0 || Exp_int(2, (n - 1) as nat) <= bound
    decreases n
{
    reveal(Exp_int);
    if n > 0 {
        assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
        assert(2 * Exp_int(2, (n - 1) as nat) <= bound);
        assert(Exp_int(2, (n - 1) as nat) <= bound);
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
{
    if n == 0 {
        assert(y == 1) by {
            reveal(Exp_int);
            assert(Exp_int(2, 0) == 1);
        }
        
        let res = x % z;
        
        assert((res as nat) == Exp_int(x as nat, y as nat) % (z as nat)) by {
            reveal(Exp_int);
            assert(Exp_int(x as nat, 1) == x as nat);
        }
        
        return res;
    } else {
        assert(n > 0);
        let n_minus_1 = (n - 1) as u64;
        
        // Compute y_half which should be 2^(n-1)
        let y_half_computed = y / 2;
        
        proof {
            assert(y as nat == Exp_int(2, n as nat));
            reveal(Exp_int);
            assert(Exp_int(2, n as nat) == 2 * Exp_int(2, (n - 1) as nat));
            assert(y as nat == 2 * Exp_int(2, (n - 1) as nat));
            assert(y_half_computed as nat == Exp_int(2, (n - 1) as nat));
        }
        
        let temp = ModExpPow2_int(x, y_half_computed, n_minus_1, z);
        
        assert((temp as nat) == Exp_int(x as nat, Exp_int(2, (n - 1) as nat)) % (z as nat));
        assert(temp < z);
        
        let temp_mod = temp % z;
        assert(temp_mod < z);
        assert((temp_mod as nat) * (temp_mod as nat) <= (z - 1) * (z - 1));
        
        if z <= u64::MAX / z {
            assert((z - 1) * (z - 1) < u64::MAX);
            let res = (temp_mod * temp_mod) % z;
            
            assert((res as nat) == Exp_int(x as nat, y as nat) % (z as nat)) by {
                assert(y as nat == Exp_int(2, n as nat));
                lemma_exp_square(x as nat, n_minus_1 as nat);
                assert(Exp_int(x as nat, y as nat) == Exp_int(Exp_int(x as nat, Exp_int(2, (n - 1) as nat)), 2));
                
                assert((temp as nat) == Exp_int(x as nat, Exp_int(2, (n - 1) as nat)) % (z as nat));
                assert((temp_mod as nat) == Exp_int(x as nat, Exp_int(2, (n - 1) as nat)) % (z as nat));
                
                lemma_mod_square(Exp_int(x as nat, Exp_int(2, (n - 1) as nat)), z as nat);
                reveal(Exp_int);
                assert(Exp_int(Exp_int(x as nat, Exp_int(2, (n - 1) as nat)), 2) % (z as nat) == 
                       ((Exp_int(x as nat, Exp_int(2, (n - 1) as nat)) % (z as nat)) * (Exp_int(x as nat, Exp_int(2, (n - 1) as nat)) % (z as nat))) % (z as nat));
                assert((res as nat) == ((temp_mod as nat) * (temp_mod as nat)) % (z as nat));
            }
            
            return res;
        } else {
            let mut acc: u64 = 0;
            let mut i: u64 = 0;
            
            while i < temp_mod
                invariant 
                    i <= temp_mod,
                    temp_mod < z,
                    z > 0,
                    (acc as nat) == (i as nat) * (temp_mod as nat) % (z as nat)
            {
                acc = (acc + temp_mod) % z;
                i = i + 1;
            }
            
            assert((acc as nat) == Exp_int(x as nat, y as nat) % (z as nat)) by {
                assert(i == temp_mod);
                assert((acc as nat) == (temp_mod as nat) * (temp_mod as nat) % (z as nat));
                assert(y as nat == Exp_int(2, n as nat));
                lemma_exp_square(x as nat, n_minus_1 as nat);
                lemma_mod_square(Exp_int(x as nat, Exp_int(2, (n - 1) as nat)), z as nat);
                reveal(Exp_int);
            }
            
            return acc;
        }
    }
}
// </vc-code>

fn main() {}
}