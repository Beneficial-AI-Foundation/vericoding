use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
decreases y
{
    if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
exec fn pow_mod_rec(x: nat, y: nat, m: nat) -> nat
  requires m > 1
  ensures result == Exp_int(x, y) % m
  decreases y
{
    if y == 0 {
        1 % m
    } else {
        let t = pow_mod_rec(x, y - 1, m);
        let res = (x * t) % m;
        proof {
            // By induction hypothesis, t == Exp_int(x, y-1) % m
            assert(t == Exp_int(x, y - 1) % m);
            // Because y > 0 in this branch, Exp_int(x,y) == x * Exp_int(x,y-1)
            assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
            // From t == Exp_int(x, y-1) % m we have (x * t) % m == (x * Exp_int(x,y-1)) % m
            assert(res == (x * Exp_int(x, y - 1)) % m);
            // Therefore res == Exp_int(x, y) % m
            assert(res == Exp_int(x, y) % m);
        }
        res
    }
}

exec fn nat_to_vec_rec(n: nat) -> Vec<char>
  ensures ValidBitString(result@)
  ensures Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        // empty vector represents 0
        Vec::<char>::new()
    } else {
        let q: nat = n / 2;
        let r: nat = n % 2;
        let mut v = nat_to_vec_rec(q);
        if r == 1 {
            v.push('1');
        } else {
            v.push('0');
        }
        proof {
            // Let full be the final sequence
            let full = v@;
            // last index
            let last_idx = full.len() as int - 1;
            // prefix is all but last
            let prefix = full.subrange(0, last_idx);
            // By induction, prefix represents q
            assert(Str2Int(prefix) == q);
            // last bit corresponds to r
            assert(full.index(last_idx) == (if r == 1 { '1' } else { '0' }));
            // By definition of Str2Int for non-empty sequences
            assert(Str2Int(full) == 2 * Str2Int(prefix) + (if full.index(last_idx) == '1' { 1 } else { 0 }));
            assert((if full.index(last_idx) == '1' { 1 } else { 0 }) == r);
            assert(Str2Int(full) == 2 * q + r);
            assert(2 * q + r == n); // division algorithm: n = 2*(n/2) + n%2
        }
        v
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let m = Str2Int(sz@);

    let num = pow_mod_rec(x, y, m);
    proof {
        // From pow_mod_rec postcondition
        assert(num == Exp_int(x, y) % m);
    }

    let res_vec = nat_to_vec_rec(num);
    proof {
        // From nat_to_vec_rec postcondition
        assert(ValidBitString(res_vec@));
        assert(Str2Int(res_vec@) == num);
        // Chain equalities to get the desired postcondition
        assert(Str2Int(res_vec@) == Exp_int(x, y) % m);
    }
    res_vec
}
// </vc-code>

fn main() {}
}