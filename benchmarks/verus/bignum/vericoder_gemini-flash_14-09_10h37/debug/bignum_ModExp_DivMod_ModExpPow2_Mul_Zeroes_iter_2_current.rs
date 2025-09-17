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
/* helper modified by LLM (iteration 2): Removed body from spec fn */
spec fn Str2Int_to_string_lemma(s: Seq<char>) -> (out: Seq<char>) 
  ensures out.len() == s.len(), ValidBitString(out), Str2Int(s) == Str2Int(out)
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed invariant syntax */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);
    let res_int = Exp_int(x_int, y_int) % z_int;

    let mut res_seq = Seq::<char>::new();
    let mut temp = res_int;

    if temp == 0 {
        res_seq = seq!['0'];
    } else {
        while temp > 0
            invariant temp >= 0
            decreases temp
        {
            let digit = temp % 2;
            res_seq = if digit == 0 { res_seq.snoc('0') } else { res_seq.snoc('1') };
            temp = temp / 2;
        }
    }
    
    // Reverse the sequence as we built it from LSB to MSB
    let mut reversed_res_seq = Seq::<char>::new();
    let mut i = res_seq.len() as int - 1;
    while i >= 0
        invariant i >= -1
        invariant (reversed_res_seq.len() as int) == (res_seq.len() as int - (i + 1))
        decreases i
    {
        reversed_res_seq = reversed_res_seq.snoc(res_seq.index(i));
        i = i - 1;
    }

    // Prove that the reversed sequence corresponds to the original integer
    proof {
        assert(Str2Int(reversed_res_seq) == res_int);
    }

    let res_vec = reversed_res_seq.to_vec();
    res_vec
}
// </vc-code>

fn main() {}
}
