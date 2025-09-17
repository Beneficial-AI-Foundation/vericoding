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
spec fn bit_of(c: char) -> nat
{
    if c == '1' { 1nat } else { 0nat }
}

proof fn lemma_str2int_extend(s: Seq<char>, i: int)
    requires
        0 <= i,
        i < s.len() as int,
        ValidBitString(s),
    ensures
        Str2Int(s.subrange(0, i + 1)) == 2nat * Str2Int(s.subrange(0, i)) + bit_of(s.index(i)),
{
}

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
}

proof fn lemma_validbit_push(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        ValidBitString(s.push(c)),
{
}

proof fn lemma_div2_mod2(n: nat)
    ensures
        n == (n / 2) * 2 + n % 2,
{
}

proof fn lemma_exp_succ(x: nat, y: nat)
    ensures
        Exp_int(x, y + 1) == x * Exp_int(x, y),
{
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires
        m > 0,
    ensures
        ((a % m) * (b % m)) % m == (a * b) % m,
{
}

/* helper modified by LLM (iteration 2): removed nat-suffixed literals and strengthened in-loop reasoning */
exec fn parse_bitstring(s: &[char]) -> (n: nat)
    requires
        ValidBitString(s@),
    ensures
        n == Str2Int(s@),
{
    let mut acc: nat = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            acc == Str2Int(s@.subrange(0, i as int)),
            ValidBitString(s@),
        decreases s.len() - i
    {
        let c = s[i];
        let bit: nat = if c == '1' { 1 as nat } else { 0 as nat };
        proof {
            assert(s@.index(i as int) == c);
            assert(bit == bit_of(c));
            assert(Str2Int(s@.subrange(0, i as int + 1))
                   == (2 as nat) * Str2Int(s@.subrange(0, i as int)) + bit_of(c));
        }
        acc = acc * (2 as nat) + bit;
        i = i + 1;
    }
    acc
}

/* helper modified by LLM (iteration 2): removed nat-suffixed literals and explicit casts for 2 and 1 */
exec fn nat_to_bitvec(n: nat) -> (r: Vec<char>)
    ensures
        ValidBitString(r@),
        Str2Int(r@) == n,
    decreases n
{
    if n == 0 {
        return Vec::<char>::new();
    }
    let mut v = nat_to_bitvec(n / (2 as nat));
    let bit_char = if n % (2 as nat) == (1 as nat) { '1' } else { '0' };
    proof {
        lemma_validbit_push(v@, bit_char);
        lemma_str2int_push(v@, bit_char);
        lemma_div2_mod2(n);
        if n % (2 as nat) == (1 as nat) {
            assert(bit_of(bit_char) == 1 as nat);
        } else {
            assert(bit_of(bit_char) == 0 as nat);
        }
    }
    v.push(bit_char);
    v
}

/* helper modified by LLM (iteration 2): removed nat-suffixed literals and explicit casts for 1 */
exec fn pow_mod_nat(x: nat, y: nat, m: nat) -> (r: nat)
    requires
        m > 0,
    ensures
        r == Exp_int(x, y) % m,
{
    let mut acc: nat = (1 as nat) % m;
    let mut i: nat = 0;
    while i < y
        invariant
            i <= y,
            acc == Exp_int(x, i) % m,
            m > 0,
        decreases y - i
    {
        proof {
            lemma_mod_mul(Exp_int(x, i), x, m);
            lemma_exp_succ(x, i);
        }
        acc = ((acc % m) * (x % m)) % m;
        i = i + (1 as nat);
    }
    acc
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
    /* code modified by LLM (iteration 2): implemented using helper parsers and modular exponentiation; removed nat-suffixed literals */
    let x = parse_bitstring(sx);
    let y = parse_bitstring(sy);
    let m = parse_bitstring(sz);
    let rnat = pow_mod_nat(x, y, m);
    let res = nat_to_bitvec(rnat);
    res
}
// </vc-code>

fn main() {}
}
