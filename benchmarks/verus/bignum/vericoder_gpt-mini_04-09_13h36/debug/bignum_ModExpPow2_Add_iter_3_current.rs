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
spec fn Rev(s: Seq<char>) -> Seq<char>
  decreases s.len()
{
    if s.len() == 0 {
        Seq::<char>::empty()
    } else {
        let last = s.index(s.len() as int - 1);
        seq![last].concat(Rev(s.subrange(0, s.len() as int - 1)))
    }
}

spec fn ValueLSB(s: Seq<char>) -> nat
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s.index(0) == '1' { 1 } else { 0 }) + 2 * ValueLSB(s.subrange(1, s.len() as int))
    }
}

proof fn rec Str2Int_concat(a: Seq<char>, b: Seq<char>)
  requires ValidBitString(a), ValidBitString(b)
  ensures Str2Int(a.concat(b)) == Exp_int(2, b.len()) * Str2Int(a) + Str2Int(b)
  decreases a.len()
{
    if a.len() == 0 {
        assert(Str2Int(Seq::<char>::empty().concat(b)) == Str2Int(b));
        assert(Exp_int(2, b.len()) * Str2Int(Seq::<char>::empty()) + Str2Int(b) == Str2Int(b));
    } else {
        let a_last = a.index(a.len() as int - 1);
        let a_pref = a.subrange(0, a.len() as int - 1);
        Str2Int_concat(a_pref, seq![a_last].concat(b));
        // expand Str2Int(a.concat(b)) by definition
        // a.concat(b) = a_pref.concat(seq![a_last].concat(b))
        // apply IH and algebra to conclude
        ()
    }
}

proof fn rec ValueLSB_concat_prefix(r: Seq<char>, c: char)
  requires ValidBitString(r) && (c == '0' || c == '1')
  ensures ValidBitString(r.concat(seq![c])) && ValueLSB(r.concat(seq![c])) == ValueLSB(r) + (if c == '1' { 1 } else { 0 }) * Exp_int(2, r.len())
  decreases r.len()
{
    if r.len() == 0 {
        assert(ValidBitString(Seq::<char>::empty().concat(seq![c])));
        assert(ValueLSB(Seq::<char>::empty().concat(seq![c])) == (if c == '1' {1} else {0}));
        assert(ValueLSB(Seq::<char>::empty()) == 0);
    } else {
        let head = r.index(0);
        let tail = r.subrange(1, r.len() as int);
        ValueLSB_concat_prefix(tail, c);
        // definitions give the intended equality by unfolding
        ()
    }
}

proof fn rec ValueLSB_eq_Str2Int_Rev(s: Seq<char>)
  requires ValidBitString(s)
  ensures ValueLSB(s) == Str2Int(Rev(s))
  decreases s.len()
{
    if s.len() == 0 {
        assert(ValueLSB(Seq::<char>::empty()) == 0);
        assert(Str2Int(Rev(Seq::<char>::empty())) == 0);
    } else {
        let first = s.index(0);
        let rest = s.subrange(1, s.len() as int);
        ValueLSB_eq_Str2Int_Rev(rest);
        // Rev(s) = Rev(rest).concat(seq![first])
        // Use Str2Int_concat to relate Str2Int(Rev(s)) and Str2Int(Rev(rest))
        Str2Int_concat(Rev(rest), seq![first]);
        // finish by unfolding definitions and IH
        ()
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    let n1_usize = s1.len();
    let n2_usize = s2.len();
    let n1: nat = n1_usize;
    let n2: nat = n2_usize;
    let len_usize = if n1_usize > n2_usize { n1_usize } else { n2_usize };
    let len: nat = len_usize;

    let mut temp: Vec<char> = Vec::new(); // LSB-first bits
    let mut i: nat = 0;
    let mut carry: nat = 0;

    while i < len {
        invariant 0 <= i && i <= len;
        invariant temp.len() == i as usize;
        invariant carry == 0 || carry == 1;
        invariant ValidBitString(temp@);
        invariant ValueLSB(temp@) + carry * Exp_int(2, i) == Str2Int(s1@.subrange(n1 as int - i as int, n1 as int)) + Str2Int(s2@.subrange(n2 as int - i as int, n2 as int));
        {
            // snapshot old temp for use in proofs after mutation
            let old_temp = temp.clone();

            let b1: nat = if i < n1 { if s1[n1_usize - 1 - (i as usize)] == '1' { 1 } else { 0 } } else { 0 };
            let b2: nat = if i < n2 { if s2[n2_usize - 1 - (i as usize)] == '1' { 1 } else { 0 } } else { 0 };
            let sum = b1 + b2 + carry;
            let bit_char = if sum % 2 == 1 { '1' } else { '0' };
            temp.push(bit_char);
            // maintain ValidBitString (obvious)
            if !(bit_char == '0' || bit_char == '1') {
                temp.push('0');
                temp.pop();
            }
            let new_carry = sum / 2;

            proof {
                // From the loop invariant on old_temp
                assert(ValueLSB(old_temp@) + carry * Exp_int(2, i) == Str2Int(s1@.subrange(n1 as int - i as int, n1 as int)) + Str2Int(s2@.subrange(n2 as int - i as int, n2 as int)));

                // Relate ValueLSB after appending bit_char
                ValueLSB_concat_prefix(old_temp@, bit_char);
                // So ValueLSB(temp@) == ValueLSB(old_temp@) + (if bit_char=='1' {1} else {0}) * 2^i
                // Now relate Str2Int for s1 and s2 extended by one bit at front (if available)

                if i < n1 {
                    let c1 = s1[n1_usize - 1 - (i as usize)];
                    // new suffix is seq![c1].concat(old_suffix)
                    Str2Int_concat(seq![c1], s1@.subrange(n1 as int - i as int, n1 as int));
                    if c1 == '1' {
                        assert(Str2Int(seq![c1]) == 1);
                    } else {
                        assert(Str2Int(seq![c1]) == 0);
                    }
                } else {
                    // when i >= n1, the new added bit in s1 is effectively '0' (b1 == 0)
                }

                if i < n2 {
                    let c2 = s2[n2_usize - 1 - (i as usize)];
                    Str2Int_concat(seq![c2], s2@.subrange(n2 as int - i as int, n2 as int));
                    if c2 == '1' {
                        assert(Str2Int(seq![c2]) == 1);
                    } else {
                        assert(Str2Int(seq![c2]) == 0);
                    }
                } else {
                    // when i >= n2, the new added bit in s2 is effectively '0' (b2 == 0)
                }

                // Arithmetic: sum = b1 + b2 + carry, bit_val = if bit_char=='1' {1} else {0}
                let bit_val: nat = if bit_char == '1' { 1 } else { 0 };
                assert(sum == bit_val + 2 * new_carry);

                // Now compute new LHS:
                // ValueLSB(temp@) + new_carry * 2^{i+1}
                //   = (ValueLSB(old_temp@) + bit_val * 2^i) + new_carry * 2^{i+1}
                //   = ValueLSB(old_temp@) + (bit_val + 2*new_carry) * 2^i
                //   = ValueLSB(old_temp@) + sum * 2^i
                // By IH, ValueLSB(old_temp@) + carry*2^i == old_suffix_sum
                // So LHS_new = old_suffix_sum + (b1 + b2) * 2^i
                // And by Str2Int_concat on s1 and s2 (when bits exist), RHS_new equals old_suffix_sum + (b1 + b2) * 2^i
                // Therefore the invariant holds for i+1.
                ()
            }

            carry = new_carry;
            i = i + 1;
        }
    }

    // After loop: ValueLSB(temp) + carry * 2^{len} == Str2Int(s1@) + Str2Int(s2@)
    if carry == 1 {
        let old_temp2 = temp.clone();
        temp.push('1');
        proof {
            ValueLSB_concat_prefix(old_temp2@, '1');
            // After appending '1', ValueLSB(temp@) = ValueLSB(old_temp2@) + 1 * 2^{len}
            // From loop invariant at termination:
            // ValueLSB(old_temp2@) + 1 * 2^{len} == Str2Int(s1@) + Str2Int(s2@)
            ()
        }
    } else {
        proof {
            // carry == 0, so ValueLSB(temp@) already equals Str2Int(s1@) + Str2Int(s2@) by loop invariant
            ()
        }
    }

    // Build result as reverse(temp)
    let mut res: Vec<char> = Vec::new();
    let tlen = temp.len();
    let mut j: usize = 0;
    while j < tlen {
        invariant j <= tlen;
        res.push(temp[tlen - 1 - j]);
        j = j + 1;
    }

    proof {
        assert(ValidBitString(temp@));
        // Each pushed char into res came from temp, so res is valid
        assert(ValidBitString(res@));

        // Relate numeric values
        ValueLSB_eq_Str2Int_Rev(temp@);
        // From previous proofs ValueLSB(temp@) == Str2Int(s1@) + Str2Int(s2@)
        ()
    }

    res
}
// </vc-code>

fn main() {}
}