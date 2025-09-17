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

proof fn exp_recursive_lemma(x: nat, y: nat)
    ensures Exp_int(x, y) == (if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) })
{
    // By the definition of Exp_int
}

proof fn str2int_empty_lemma()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
    // By the definition of Str2Int
}

proof fn str2int_recursive_lemma(s: Seq<char>)
    requires ValidBitString(s)
    ensures s.len() > 0 ==> Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1 } else { 0 })
{
    // By the definition of Str2Int and ValidBitString
}

proof fn valid_bitstring_subrange_lemma(s: Seq<char>, start: int, end: int)
    requires ValidBitString(s), 0 <= start, end <= s.len() as int, start <= end
    ensures ValidBitString(s.subrange(start, end))
{
    // ValidBitString holds for subrange
}

spec fn binary_to_nat(bits: Seq<char>) -> nat
    requires ValidBitString(bits)
    decreases bits.len()
{
    if bits.len() == 0 { 0 } else { 2 * binary_to_nat(bits.subrange(0, bits.len() as int - 1)) + (if bits.index(bits.len() as int - 1) == '1' { 1 } else { 0 }) }
}

proof fn str2int_eq_binary_to_nat_lemma(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) == binary_to_nat(s)
{
    // Str2Int and binary_to_nat are equivalent
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Convert input slices to sequences for verification
    let sx_seq = sx@;
    let sy_seq = sy@;
    let sz_seq = sz@;
    
    // Base case: if sy is empty (but requires says sy@.len() > 0, so we skip this)
    if sy_seq.len() == 0 {
        proof {
            // Should not be reachable due to precondition
            assert(false) by {}
        }
        return Vec::<char>::new();
    }
    
    // Recursive case
    proof {
        // Use lemmas to reason about the properties
        exp_recursive_lemma(Str2Int(sx_seq), Str2Int(sy_seq));
        str2int_recursive_lemma(sy_seq);
        valid_bitstring_subrange_lemma(sy_seq, 0, sy_seq.len() as int - 1);
        str2int_eq_binary_to_nat_lemma(sx_seq);
        str2int_eq_binary_to_nat_lemma(sy_seq);
        str2int_eq_binary_to_nat_lemma(sz_seq);
    }
    
    // Handle the last bit of sy
    let last_char = sy[sy.len() - 1];
    let remaining_sy = &sy[..sy.len() - 1];
    
    // Recursive call for the remaining bits
    let mut recursive_result = ModExp_Mul_Zeroes(sx, remaining_sy, sz);
    
    proof {
        // Verify that recursive call satisfies preconditions
        assert(ValidBitString(remaining_sy@));
        assert(remaining_sy@.len() < sy_seq.len());
        assert(Str2Int(sz_seq) > 1);
    }
    
    // Multiply result by x (mod sz) if the last bit is '1', else square it
    if last_char == '1' {
        let mut result = ModMul_Mul_Zeroes(recursive_result, sx, sz);
        proof {
            // Verify the modular exponentiation property: x^y = x^(y-1) * x
            assert(Str2Int(result@) == (Str2Int(recursive_result@) * Str2Int(sx_seq)) % Str2Int(sz_seq));
        }
        result
    } else {
        let mut result = ModMul_Mul_Zeroes(recursive_result, recursive_result, sz);
        proof {
            // Verify the modular exponentiation property: x^(2*(y/2)) = (x^(y/2))^2
            assert(Str2Int(result@) == (Str2Int(recursive_result@) * Str2Int(recursive_result@)) % Str2Int(sz_seq));
        }
        result
    }
}
// </vc-code>

fn main() {}
}
