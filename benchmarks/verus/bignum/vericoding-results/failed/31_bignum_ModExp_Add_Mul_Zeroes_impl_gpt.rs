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
/* helper modified by LLM (iteration 7): interpret a bit character as nat 0/1 */
spec fn bit_of(c: char) -> nat { if c == '1' { 1nat } else { 0nat } }

/* helper modified by LLM (iteration 7): lemma preserving ValidBitString on push */
proof fn lemma_validbit_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
{
    let t = s.push(c);
    assert forall |i: int|
        0 <= i && i < t.len() as int implies (t.index(i) == '0' || t.index(i) == '1')
    by
    {
        if 0 <= i && i < t.len() as int {
            let sl = s.len() as int;
            assert(t.len() as int == sl + 1);
            if i < sl {
                assert(0 <= i && i < sl);
                assert(t.index(i) == s.index(i));
                assert(s.index(i) == '0' || s.index(i) == '1');
            } else {
                assert(i == sl);
                assert(t.index(i) == c);
                assert(c == '0' || c == '1');
            }
        }
    }
}

/* helper modified by LLM (iteration 7): lemma for Str2Int after push */
proof fn lemma_str2int_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s.push(c)) == 2nat * Str2Int(s) + bit_of(c),
{
    let t = s.push(c);
    assert(t.len() > 0);
    assert(t.subrange(0, t.len() as int - 1) == s);
    assert(t.index(t.len() as int - 1) == c);
    assert(
        Str2Int(t)
        == 2nat * Str2Int(t.subrange(0, t.len() as int - 1))
           + (if t.index(t.len() as int - 1) == '1' { 1nat } else { 0nat })
    );
}

/* helper modified by LLM (iteration 7): executable helper computing Str2Int of a valid bit-slice */
fn str2int_exec(s: &[char]) -> (r: nat)
    requires
        ValidBitString(s@),
    ensures
        r == Str2Int(s@),
{
    let mut acc: nat = 0nat;
    let mut i: int = 0;
    while i < s.len() as int
        invariant
            0 <= i && i <= s.len() as int,
            ValidBitString(s@),
            acc == Str2Int(s@.subrange(0, i)),
        decreases s.len() as int - i
    {
        let c = s[i as usize];
        let bit: nat = if c == '1' { 1nat } else { 0nat };
        proof {
            assert(0 <= i && i < s.len() as int);
            assert(s@.index(i) == c);
            assert(ValidBitString(s@));
            assert(c == '0' || c == '1');
            let t = s@.subrange(0, (i + 1) as int);
            assert(t.len() > 0);
            assert(t.subrange(0, t.len() as int - 1) == s@.subrange(0, i));
            assert(t.index(t.len() as int - 1) == c);
            assert(
                Str2Int(t)
                == 2nat * Str2Int(t.subrange(0, t.len() as int - 1))
                   + (if t.index(t.len() as int - 1) == '1' { 1nat } else { 0nat })
            );
            assert(2nat * Str2Int(s@.subrange(0, i)) + bit == Str2Int(t));
        }
        acc = 2nat * acc + bit;
        i = i + 1;
        proof { assert(acc == Str2Int(s@.subrange(0, i))); }
    }
    acc
}

/* helper modified by LLM (iteration 7): executable helper converting nat to bitstring (possibly with leading zero) */
fn nat_to_bits_exec(n: nat) -> (v: Vec<char>)
    ensures
        ValidBitString(v@),
        Str2Int(v@) == n,
    decreases n
{
    if n == 0nat {
        let mut r: Vec<char> = Vec::new();
        r.push('0');
        return r;
    }
    let q: nat = n / 2nat;
    let rbit: nat = n % 2nat;
    let mut v = nat_to_bits_exec(q);
    let c: char = if rbit == 1nat { '1' } else { '0' };
    proof { assert(c == '0' || c == '1'); }
    let ghost s_prev = v@;
    v.push(c);
    proof {
        // Validity after push
        lemma_validbit_push(s_prev, c);
        assert(v@ == s_prev.push(c));
        // Value after push
        lemma_str2int_push(s_prev, c);
        assert(bit_of(c) == rbit) by {
            if rbit == 1nat { assert(c == '1'); } else { assert(c == '0'); }
        }
        assert(Str2Int(s_prev) == q);
        assert(Str2Int(v@) == 2nat * Str2Int(s_prev) + bit_of(c));
        assert(2nat * q + rbit == n);
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): compute modular exponent on nats and convert remainder to bitstring */
    let base_n: nat = str2int_exec(sx);
    let exp_n: nat = str2int_exec(sy);
    let mod_n: nat = str2int_exec(sz);

    let mut acc_pow: nat = 1nat;
    let mut i: nat = 0nat;
    while i < exp_n
        invariant
            i <= exp_n,
            acc_pow == Exp_int(base_n, i),
        decreases exp_n - i
    {
        let ghost i_old = i;
        let ghost acc_old = acc_pow;
        acc_pow = base_n * acc_pow;
        i = i + 1nat;
        proof {
            assert(i > 0nat);
            assert(i == i_old + 1nat);
            assert(Exp_int(base_n, i) == base_n * Exp_int(base_n, (i - 1) as nat));
            assert(Exp_int(base_n, (i - 1) as nat) == Exp_int(base_n, i_old));
            assert(acc_pow == base_n * acc_old);
            assert(acc_old == Exp_int(base_n, i_old));
            assert(acc_pow == Exp_int(base_n, i));
        }
    }

    let rem: nat = acc_pow % mod_n;
    let res_vec: Vec<char> = nat_to_bits_exec(rem);
    proof {
        assert(base_n == Str2Int(sx@));
        assert(exp_n == Str2Int(sy@));
        assert(mod_n == Str2Int(sz@));
        assert(acc_pow == Exp_int(base_n, exp_n));
        assert(Str2Int(res_vec@) == rem);
        assert(Str2Int(res_vec@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }
    res_vec
}
// </vc-code>

fn main() {}
}
