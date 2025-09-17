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
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_int(x: u64, y: u64, n: u64, z: u64) -> (res: u64)
  requires z > 0u64,
   (y as nat) == Exp_int(2, n as nat)
  ensures (res as nat) == Exp_int(x as nat, y as nat) % (z as nat)
  decreases n
// </vc-spec>
// <vc-code>
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
// </vc-code>

fn main() {}
}