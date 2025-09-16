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
/* helper modified by LLM (iteration 8): spec executable exponentiation */
spec fn Exp_exec_spec(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * Exp_exec_spec(x, (y - 1) as nat) }
}

/* helper modified by LLM (iteration 8): proof relating Exp_int to Exp_exec_spec */
proof fn exp_exec_spec_equiv(x: nat, y: nat)
    ensures Exp_int(x, y) == Exp_exec_spec(x, y),
    decreases y
{
    if y == 0 {
    } else {
        let y1: nat = (y - 1) as nat;
        exp_exec_spec_equiv(x, y1);
        assert(Exp_int(x, y) == x * Exp_int(x, y1));
        assert(Exp_exec_spec(x, y) == x * Exp_exec_spec(x, y1));
        assert(Exp_int(x, y1) == Exp_exec_spec(x, y1));
        assert(Exp_int(x, y) == Exp_exec_spec(x, y));
    }
}

/* helper modified by LLM (iteration 8): spec version of Str2Int for proofs */
spec fn Str2Int_spec(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Str2Int_spec(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

/* helper modified by LLM (iteration 8): proof relating Str2Int to Str2Int_spec */
proof fn str2int_spec_equiv(s: Seq<char>)
    requires ValidBitString(s),
    ensures Str2Int(s) == Str2Int_spec(s),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        str2int_spec_equiv(prefix);
        assert(Str2Int(s) == 2 * Str2Int(prefix) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int_spec(s) == 2 * Str2Int_spec(prefix) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(prefix) == Str2Int_spec(prefix));
        assert(Str2Int(s) == Str2Int_spec(s));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): compute modular exponentiation using u128 with loop decreases */
{
    let mut base_u128: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < sx.len()
        invariant
            true,
        decreases sx.len() - i
    {
        let bit = if sx[i] == '1' { 1u128 } else { 0u128 };
        base_u128 = base_u128 * 2u128 + bit;
        i += 1usize;
    }

    let mut exp_u128: u128 = 0u128;
    let mut j: usize = 0usize;
    while j < sy.len()
        invariant
            true,
        decreases sy.len() - j
    {
        let bit = if sy[j] == '1' { 1u128 } else { 0u128 };
        exp_u128 = exp_u128 * 2u128 + bit;
        j += 1usize;
    }

    let mut m_u128: u128 = 0u128;
    let mut k: usize = 0usize;
    while k < sz.len()
        invariant
            true,
        decreases sz.len() - k
    {
        let bit = if sz[k] == '1' { 1u128 } else { 0u128 };
        m_u128 = m_u128 * 2u128 + bit;
        k += 1usize;
    }

    let mut result_u128: u128 = 1u128 % m_u128;
    let mut base_mod: u128 = base_u128 % m_u128;
    let mut e: u128 = exp_u128;
    let mut e_usize: usize = exp_u128 as usize;
    while e > 0u128
        invariant
            true,
        decreases e_usize
    {
        if e % 2u128 == 1u128 {
            result_u128 = (result_u128 * base_mod) % m_u128;
        }
        base_mod = (base_mod * base_mod) % m_u128;
        e = e / 2u128;
        e_usize = e as usize;
    }

    let mut res: Vec<char> = Vec::new();
    if result_u128 == 0u128 {
        // represent 0 as empty vector
    } else {
        let mut tmp: Vec<char> = Vec::new();
        let mut t: u128 = result_u128;
        let mut t_usize: usize = t as usize;
        while t > 0u128
            invariant
                true,
            decreases t_usize
        {
            let b = if t % 2u128 == 1u128 { '1' } else { '0' };
            tmp.push(b);
            t = t / 2u128;
            t_usize = t as usize;
        }
        let mut p: usize = tmp.len();
        while p > 0usize
            invariant
                true,
            decreases p
        {
            p -= 1usize;
            res.push(tmp[p]);
        }
    }
    res
}

// </vc-code>

fn main() {}
}
