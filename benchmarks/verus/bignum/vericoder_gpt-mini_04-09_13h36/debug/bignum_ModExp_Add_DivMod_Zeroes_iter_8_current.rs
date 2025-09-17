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
        let r = 1 % m;
        proof {
            assert(Exp_int(x, 0) == 1);
            assert(r == Exp_int(x, 0) % m);
        }
        return r;
    } else {
        proof { assert(y > 0); }
        let t = pow_mod_rec(x, (y - 1) as nat, m);
        let res = (x * t) % m;
        proof {
            assert(t == Exp_int(x, y - 1) % m);
            assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
            assert(res == (x * Exp_int(x, y - 1)) % m);
            assert(res == Exp_int(x, y) % m);
        }
        return res;
    }
}

proof fn div_mod_2_lemma(n: nat)
  ensures n == 2*(n / 2) + n % 2 && (n % 2 == 0 || n % 2 == 1)
  decreases n
{
    assert(n == 2*(n / 2) + n % 2);
    assert(n % 2 == 0 || n % 2 == 1);
}

exec fn nat_to_vec_rec(n: nat) -> Vec<char>
  ensures ValidBitString(result@)
  ensures Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        let v = Vec::<char>::new();
        proof {
            assert(ValidBitString(v@));
            assert(Str2Int(v@) == 0);
        }
        return v;
    } else {
        let q: nat = n / 2;
        let r: nat = n % 2;
        let mut prefix = nat_to_vec_rec(q);
        proof {
            assert(ValidBitString(prefix@));
            assert(Str2Int(prefix@) == q);
        }
        let b = if r == 1 { '1' } else { '0' };
        let old = prefix.clone();
        prefix.push(b);
        proof {
            let full = prefix@;
            let last_idx = full.len() as int - 1;
            assert(full.subrange(0, last_idx) == old@);
            assert(Str2Int(full.subrange(0, last_idx)) == q);
            assert(full.index(last_idx) == b);
            assert(ValidBitString(old@));
            assert(b == '0' || b == '1');
            assert(ValidBitString(full));
            assert(Str2Int(full) == 2 * Str2Int(full.subrange(0, last_idx)) + (if full.index(last_idx) == '1' { 1 } else { 0 }));
            assert((if full.index(last_idx) == '1' { 1 } else { 0 }) == r);
            div_mod_2_lemma(n);
            assert(2 * q + r == n);
            assert(Str2Int(full) == 2 * q + r);
            assert(Str2Int(full) == n);
        }
        return prefix;
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
    let x: nat = Str2Int(sx@);
    let y: nat = Str2Int(sy@);
    let m: nat = Str2Int(sz@);

    proof {
        assert(m > 1);
    }
    let num = pow_mod_rec(x, y, m);
    proof {
        assert(num == Exp_int(x, y) % m);
    }

    let res_vec = nat_to_vec_rec(num);
    proof {
        assert(ValidBitString(res_vec@));
        assert(Str2Int(res_vec@) == num);
        assert(Str2Int(res_vec@) == Exp_int(x, y) % m);
    }
    res_vec
}
// </vc-code>

fn main() {}
}