use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
proof fn lemma_exp_int_multiply(x: nat, a: nat, b: nat)
    ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
    decreases b
{
    if b == 0 {
        assert(Exp_int(x, a + 0) == Exp_int(x, a));
        assert(Exp_int(x, 0) == 1);
    } else {
        lemma_exp_int_multiply(x, a, (b - 1) as nat);
        assert(Exp_int(x, a + b) == x * Exp_int(x, a + (b - 1) as nat));
    }
}

proof fn lemma_exp_square(x: nat, n: nat)
    ensures Exp_int(x, Exp_int(2, n)) == if n == 0 { x } else { Exp_int(Exp_int(x, Exp_int(2, (n - 1) as nat)), 2) }
    decreases n
{
    if n == 0 {
        assert(Exp_int(2, 0) == 1);
        assert(Exp_int(x, 1) == x);
    } else {
        assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
        lemma_exp_int_multiply(x, Exp_int(2, (n - 1) as nat), Exp_int(2, (n - 1) as nat));
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
        assert(y == 1u64);
        let res = (x % z) as u64;
        assert((res as nat) == (x as nat) % (z as nat));
        assert(Exp_int(x as nat, 1) == x as nat);
        return res;
    } else {
        let y_half = y / 2;
        assert(y_half == Exp_int(2, (n - 1) as nat));
        let half_result = ModExpPow2_int(x, y_half, n - 1, z);
        proof {
            lemma_exp_square(x as nat, n as nat);
            assert(Exp_int(x as nat, y as nat) == Exp_int(Exp_int(x as nat, y_half as nat), 2));
            assert(Exp_int(half_result as nat, 2) % (z as nat) == ((half_result as nat) * (half_result as nat)) % (z as nat));
        }
        let squared = ((half_result as u128 * half_result as u128) % (z as u128)) as u64;
        assert((squared as nat) == Exp_int(half_result as nat, 2) % (z as nat));
        return squared;
    }
}
// </vc-code>

fn main() {}
}


