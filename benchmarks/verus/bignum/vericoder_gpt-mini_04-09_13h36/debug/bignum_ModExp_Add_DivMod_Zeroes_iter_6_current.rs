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
        r
    } else {
        let t = pow_mod_rec(x, y - 1, m);
        let res = (x * t) % m;
        proof {
            // By induction hypothesis
            assert(t == Exp_int(x, y - 1) % m);
            // Expand Exp_int
            assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
            // Relate res to Exp_int
            assert(res == (x * Exp_int(x, y - 1)) % m);
            assert(res == Exp_int(x, y) % m);
        }
        res
    }
}

proof fn div_mod_2_lemma(n: nat)
  ensures n == 2*(n / 2) + n % 2 && (n % 2 == 0 || n % 2 == 1)
  decreases n
{
    // These equalities are definitionally true for builtin div/mod;
    // asserting them helps the verifier use them in subsequent proofs.
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
            // empty sequence is a valid bit string and represents 0
            assert(ValidBitString(v@));
            assert(Str2Int(v@) == 0);
        }
        v
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
            // prefix (all but last) equals old@
            assert(full.subrange(0, last_idx) == old@);
            // by IH prefix represents q
            assert(Str2Int(full.subrange(0, last_idx)) == q);
            // full is a valid bit string (prefix valid and last is '0' or '1')
            assert(full.index(last_idx) == b);
            assert(ValidBitString(old@));
            assert(b == '0' || b == '1');
            assert(ValidBitString(full));
            // Str2Int for non-empty sequence
            assert(Str2Int(full) == 2 * Str2Int(full.subrange(0, last_idx)) + (if full.index(last_idx) == '1' { 1 } else { 0 }));
            // relate bit value to r
            assert((if full.index(last_idx) == '1' { 1 } else { 0 }) == r);
            // use division lemma to connect q,r and n
            div_mod_2_lemma(n);
            assert(2 * q + r == n);
            assert(Str2Int(full) == 2 * q + r);
            assert(Str2Int(full) == n);
        }
        prefix
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