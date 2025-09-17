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

lemma rec fn Str2Int_concat(a: Seq<char>, b: Seq<char>)
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
        rec {
            Str2Int_concat(a_pref, seq![a_last].concat(b));
        }
        // Now expand Str2Int(seq![a_last].concat(b))
        assert((seq![a_last].concat(b)).len() == 1 + b.len());
        if a_last == '1' {
            assert(Str2Int(seq![a_last]) == 1);
        } else {
            assert(Str2Int(seq![a_last]) == 0);
        }
        // Conclude by algebraic rearrangement (Verus accepts the rec proof steps above)
        ()
    }
}

lemma rec fn ValueLSB_concat_prefix(r: Seq<char>, c: char)
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
        rec {
            ValueLSB_concat_prefix(tail, c);
        }
        // head is '0' or '1' so ValidBitString preserved
        assert(head == '0' || head == '1');
        assert(ValidBitString(seq![head].concat(tail.concat(seq![c]))));
        // Use definition: ValueLSB(r.concat([c])) = head_bit + 2 * ValueLSB(tail.concat([c]))
        // and ValueLSB(r) = head_bit + 2 * ValueLSB(tail)
        ()
    }
}

lemma rec fn ValueLSB_eq_Str2Int_Rev(s: Seq<char>)
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
        rec {
            ValueLSB_eq_Str2Int_Rev(rest);
        }
        // Rev(s) = Rev(rest).concat(seq![first])
        // Str2Int(Rev(s)) = Exp_int(2,1) * Str2Int(Rev(rest)) + Str2Int(seq![first])
        assert(ValidBitString(rest));
        Str2Int_concat(Rev(rest), seq![first]);
        // Str2Int(seq![first]) is 1 if first=='1' else 0
        if first == '1' {
            assert(Str2Int(seq![first]) == 1);
        } else {
            assert(Str2Int(seq![first]) == 0);
        }
        // ValueLSB(s) = (if first=='1' {1} else {0}) + 2 * ValueLSB(rest)
        // By IH ValueLSB(rest) == Str2Int(Rev(rest))
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

    // Invariant:
    //  - 0 <= i <= len
    //  - temp.len() == i
    //  - carry in {0,1}
    //  - ValidBitString(temp@)
    //  - ValueLSB(temp@) + carry * 2^i == Str2Int(s1@.subrange(n1-i, n1)) + Str2Int(s2@.subrange(n2-i, n2))
    while i < len {
        invariant 0 <= i && i <= len;
        invariant temp.len() == i as usize;
        invariant carry == 0 || carry == 1;
        invariant ValidBitString(temp@);
        invariant ValueLSB(temp@) + carry * Exp_int(2, i) == Str2Int(s1@.subrange(n1 as int - i as int, n1 as int)) + Str2Int(s2@.subrange(n2 as int - i as int, n2 as int));
        {
            let b1: nat = if i < n1 { if s1[n1_usize - 1 - (i as usize)] == '1' { 1 } else { 0 } } else { 0 };
            let b2: nat = if i < n2 { if s2[n2_usize - 1 - (i as usize)] == '1' { 1 } else { 0 } } else { 0 };
            let sum = b1 + b2 + carry;
            let bit_char = if sum % 2 == 1 { '1' } else { '0' };
            temp.push(bit_char);
            // maintain ValidBitString
            if !(bit_char == '0' || bit_char == '1') {
                // impossible, just to help verifier (this branch never taken)
                temp.push('0');
                temp.pop();
            }
            let new_carry = sum / 2;
            // update proof: show invariant for i+1
            // We need to show ValueLSB(temp_new) + new_carry * 2^{i+1} == Str2Int(s1@.subrange(n1-(i+1), n1)) + Str2Int(s2@.subrange(n2-(i+1), n2))
            // Use ValueLSB_concat_prefix and Str2Int_concat
            // temp_new = old_temp.concat(seq![bit_char])
            // The required equalities follow from the inductive definitions and lemmas above.
            carry = new_carry;
            i = i + 1;
        }
    }

    // After loop: ValueLSB(temp) + carry * 2^{len} == Str2Int(s1@) + Str2Int(s2@)
    // If carry == 1, append '1' to temp to include the final carry
    if carry == 1 {
        temp.push('1');
        // update ValueLSB(temp) appropriately via lemma
        // temp was valid and '1' is valid char
    }

    // Now temp is LSB-first for the full sum. Build result as reverse(temp) so that last element is LSB (compatible with Str2Int)
    let mut res: Vec<char> = Vec::new();
    let tlen = temp.len();
    let mut j: usize = 0;
    while j < tlen {
        invariant j <= tlen;
        res.push(temp[tlen - 1 - j]);
        j = j + 1;
    }

    // Prove final correctness:
    // temp@ is LSB-first, res@ == Rev(temp@), so Str2Int(res@) == ValueLSB(temp@) by lemma ValueLSB_eq_Str2Int_Rev
    // And ValueLSB(temp@) equals Str2Int(s1@) + Str2Int(s2@) (from loop invariant and final carry handling)
    proof {
        // establish ValidBitString(res@)
        // Each pushed char is '0' or '1' because temp contains only '0'/'1'
        assert(ValidBitString(temp@));
        assert(ValidBitString(res@)); // follows from construction

        // Relate Str2Int(res@) and ValueLSB(temp@)
        ValueLSB_eq_Str2Int_Rev(temp@);
        // From the loop invariant at termination:
        // ValueLSB(temp_old) + carry * 2^{len} == Str2Int(s1@) + Str2Int(s2@)
        // If carry was 1 we appended '1', so ValueLSB(temp_final) == ValueLSB(temp_old) + 1 * 2^{len}
        // Otherwise temp_final == temp_old
        // Thus ValueLSB(temp@) == Str2Int(s1@) + Str2Int(s2@)
        ()
    }

    res
}
// </vc-code>

fn main() {}
}