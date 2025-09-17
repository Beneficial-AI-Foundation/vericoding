use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
proof fn power_of_2_div_lemma(n: nat)
    requires
        n > 0
    ensures
        Exp_int(2, n) / 2 == Exp_int(2, (n - 1) as nat)
{
    unfold(Exp_int(2, n));
}

proof fn lemma_exp_plus(x: nat, y1: nat, y2: nat)
    ensures
        Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
    decreases y1
{
    if y1 > 0 {
        lemma_exp_plus(x, (y1 - 1) as nat, y2);
        vstd::math::lemma_mul_is_associative(x, Exp_int(x, (y1 - 1) as nat), Exp_int(x, y2));
        assert(Exp_int(x, y1) == x * Exp_int(x, (y1-1) as nat)) by { unfold(Exp_int(x,y1)); };
        assert(Exp_int(x, y1+y2) == x * Exp_int(x, y1+y2-1)) by { unfold(Exp_int(x,y1+y2)); };
    }
}

proof fn lemma_exp_square(x: nat, y: nat)
    ensures
        Exp_int(x, 2*y) == Exp_int(x, y) * Exp_int(x, y)
{
    lemma_exp_plus(x, y, y);
    assert(y+y == 2*y);
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
        return x % z;
    } else {
        let y_rec = y / 2;
        let n_rec = n - 1;
        
        proof {
            power_of_2_div_lemma(n as nat);
            assert((y_rec as nat) == Exp_int(2, n_rec as nat));
        }

        let t = ModExpPow2_int(x, y_rec, n_rec, z);

        let t_128 = t as u128;
        let z_128 = z as u128;
        let res_128 = (t_128 * t_128) % z_128;
        let res = res_128 as u64;

        proof {
            let x_nat = x as nat;
            let z_nat = z as nat;
            let y_nat = y as nat;
            let n_nat = n as nat;
            let n_rec_nat = n_rec as nat;

            let exp_rec_nat = Exp_int(2, n_rec_nat);
            lemma_exp_square(x_nat, exp_rec_nat);
            
            assert(y_nat == 2 * exp_rec_nat) by {
                power_of_2_div_lemma(n_nat);
                assert(Exp_int(2, n_nat) == y_nat);
                vstd::math::lemma_mul_division_auto(y_nat, 2);
            };

            vstd::math::lemma_mod_properties_auto();

            let A = Exp_int(x_nat, exp_rec_nat);
            assert(Exp_int(x_nat, y_nat) % z_nat == (A * A) % z_nat);
            assert((A * A) % z_nat == ((A % z_nat) * (A % z_nat)) % z_nat);
            
            assert((t as nat) == A % z_nat);
            
            assert((res as nat) == ((t as nat) * (t as nat)) % z_nat);
        }
        res
    }
}
// </vc-code>

fn main() {}
}


