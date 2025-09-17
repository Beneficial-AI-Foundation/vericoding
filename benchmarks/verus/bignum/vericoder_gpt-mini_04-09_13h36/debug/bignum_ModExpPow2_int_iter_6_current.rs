use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
proof fn exp_add(x: nat, a: nat, b: nat) -> ()
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
    if b == 0 {
        // Exp_int(x, a + 0) == Exp_int(x, a)
        assert(Exp_int(x, a + 0) == Exp_int(x, a));
        assert(Exp_int(x, 0) == 1);
        assert(Exp_int(x, a) * Exp_int(x, 0) == Exp_int(x, a) * 1);
        assert(Exp_int(x, a + 0) == Exp_int(x, a) * Exp_int(x, 0));
    } else {
        // b > 0
        // Exp_int(x, a + b) = x * Exp_int(x, a + b - 1)
        assert(a + b >= 1);
        let b1 = b - 1;
        // Use recursion on b1
        exp_add(x, a, b1);
        // From definition:
        assert(Exp_int(x, a + b) == x * Exp_int(x, a + b1));
        // By inductive hypothesis:
        assert(Exp_int(x, a + b1) == Exp_int(x, a) * Exp_int(x, b1));
        // So:
        assert(Exp_int(x, a + b) == x * (Exp_int(x, a) * Exp_int(x, b1)));
        assert(Exp_int(x, a + b) == Exp_int(x, a) * (x * Exp_int(x, b1)));
        // And x * Exp_int(x, b1) == Exp_int(x, b)
        assert(x * Exp_int(x, b1) == Exp_int(x, b));
        assert(Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b));
    }
}

proof fn mod_mul_congr(a: nat, z: nat) -> ()
  requires z > 0
  ensures ((a % z) * (a % z)) % z == (a * a) % z
{
    // Let q = a / z, r = a % z, so a = z*q + r
    let q = a / z;
    let r = a % z;
    assert(a == z * q + r);
    // Expand (z*q + r)*(z*q + r) = z*(z*q*q + 2*q*r) + r*r
    assert((a * a) == (z * q + r) * (z * q + r));
    assert((a * a) == z * (z * q * q + 2 * q * r) + r * r);
    // So (a*a) % z == (r*r) % z
    assert((a * a) % z == (r * r) % z);
    // And (a % z) == r, so ((a%z)*(a%z))%z == (r*r)%z
    assert((a % z) == r);
    assert(((a % z) * (a % z)) % z == (r * r) % z);
    // Thus ((a%z)*(a%z))%z == (a*a)%z
    assert(((a % z) * (a % z)) % z == (a * a) % z);
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
    let mut cur: u64 = x % z;
    let mut i: u64 = 0;
    proof {
        // establish initial invariant: i == 0 and cur == x % z == Exp_int(x, Exp_int(2,0)) % z
        assert((i as nat) == 0);
        assert(Exp_int(2, 0) == 1);
        assert(Exp_int(x as nat, Exp_int(2, 0)) == Exp_int(x as nat, 1));
        assert(Exp_int(x as nat, 1) == x as nat);
        assert((cur as nat) == (x as nat) % (z as nat));
        assert((cur as nat) == (Exp_int(x as nat, Exp_int(2, i as nat)) % (z as nat)));
    }
    while i < n
        invariant (i as nat) <= (n as nat)
        invariant (cur as nat) == (Exp_int(x as nat, Exp_int(2, i as nat)) % (z as nat))
        decreases (n as nat) - (i as nat)
    {
        let old_cur = cur;
        proof {
            let A: nat = Exp_int(x as nat, Exp_int(2, i as nat));
            let B: nat = Exp_int(2, i as nat);
            // From invariant: old_cur == A % z
            assert((old_cur as nat) == A % (z as nat));
            // Ensure modulus > 0 for mod_mul_congr
            assert((z as nat) > 0);
            // mod multiplication congruence: ((A%z)*(A%z))%z == (A*A)%z
            mod_mul_congr(A, z as nat);
            // So ((old_cur*old_cur)%z) == (A*A)%z
            assert(((old_cur as nat) * (old_cur as nat)) % (z as nat) == (A * A) % (z as nat));
            // By exp_add: A*A == Exp_int(x, B + B)
            exp_add(x as nat, B, B);
            assert(A * A == Exp_int(x as nat, B + B));
            // Show B + B == Exp_int(2, i+1)
            assert(Exp_int(2, (i as nat) + 1) == 2 * B);
            assert(2 * B == B + B);
            assert(B + B == Exp_int(2, (i as nat) + 1));
            // Combine to get ((old_cur*old_cur)%z) == Exp_int(x, Exp_int(2, i+1)) % z
            assert(((old_cur as nat) * (old_cur as nat)) % (z as nat) == Exp_int(x as nat, Exp_int(2, (i as nat) + 1)) % (z as nat));
        }
        cur = (old_cur * old_cur) % z;
        i = i + 1;
    }
    let res = cur;
    proof {
        // From loop invariant at i == n:
        assert((res as nat) == Exp_int(x as nat, Exp_int(2, (n as nat))) % (z as nat));
        // Use precondition y == Exp_int(2, n)
        assert(Exp_int(x as nat, Exp_int(2, (n as nat))) == Exp_int(x as nat, y as nat));
        assert((res as nat) == Exp_int(x as nat, y as nat) % (z as nat));
    }
    res
}
// </vc-code>

fn main() {}
}