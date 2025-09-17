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

proof fn Str2Int_concat(a: Seq<char>, b: Seq<char>)
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
        ()
    }
}

proof fn ValueLSB_concat_prefix(r: Seq<char>, c: char)
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
        ()
    }
}

proof fn ValueLSB_eq_Str2Int_Rev(s: Seq<char>)
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
        Str2Int_concat(Rev(rest), seq![first]);
        ()
    }
}

proof fn Str2Int_singleton(c: char)
  requires c == '0' || c == '1'
  ensures Str2Int(seq![c]) == (if c == '1' {1} else {0})
{
    if c == '0' {
        assert(Str2Int(seq!['0']) == 0);
    } else {
        assert(Str2Int(seq!['1']) == 1);
    }
}

proof fn ValidBitString_subrange(s: Seq<char>, start: int, end: int)
  requires ValidBitString(s)
  requires 0 <= start && start <= end && end <= s.len() as int
  ensures ValidBitString(s.subrange(start, end))
  decreases s.len()
{
    forall(|i: int| (0 <= i && i < (end - start)) ==> {
        // s.subrange(start, end).index(i) == s.index(start + i)
        assert(s.subrange(start, end).index(i) == s.index(start + i));
        assert(s.index(start + i) == '0' || s.index(start + i) == '1');
    });
    ()
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

    while i < len
        invariant i <= len;
        invariant temp.len() == i as usize;
        invariant carry == 0 || carry == 1;
        invariant ValidBitString(temp@);
        invariant ValueLSB(temp@) + carry * Exp_int(2, i) ==
            Str2Int(s1@.subrange(if i as int <= n1 as int { n1 as int - i as int } else { 0 }, n1 as int))
            + Str2Int(s2@.subrange(if i as int <= n2 as int { n2 as int - i as int } else { 0 }, n2 as int));
    {
        let old_temp = temp.clone();

        let b1: nat = if i < n1 { if s1[n1_usize - 1 - (i as usize)] == '1' { 1 } else { 0 } } else { 0 };
        let b2: nat = if i < n2 { if s2[n2_usize - 1 - (i as usize)] == '1' { 1 } else { 0 } } else { 0 };
        let sum = b1 + b2 + carry;
        let bit_char = if sum % 2 == 1 { '1' } else { '0' };
        temp.push(bit_char);
        let new_carry = sum / 2;

        proof {
            // Old invariant
            assert(ValueLSB(old_temp@) + carry * Exp_int(2, i) ==
                Str2Int(s1@.subrange(if i as int <= n1 as int { n1 as int - i as int } else { 0 }, n1 as int))
                + Str2Int(s2@.subrange(if i as int <= n2 as int { n2 as int - i as int } else { 0 }, n2 as int)));

            // Append bit relation
            assert(bit_char == '0' || bit_char == '1');
            ValueLSB_concat_prefix(old_temp@, bit_char);
            let bit_val: nat = if bit_char == '1' { 1 } else { 0 };
            assert(ValueLSB(temp@) == ValueLSB(old_temp@) + bit_val * Exp_int(2, i));

            // Relate sum decomposition: sum == bit_val + 2 * new_carry
            assert(sum == bit_val + 2 * new_carry);

            // Prepare to relate s1 subranges for i and i+1
            if i < n1 {
                let start_old1 = n1 as int - i as int;
                let start_new1 = start_old1 - 1;
                let c1 = s1[n1_usize - 1 - (i as usize)];
                // ensure validity of singleton subrange
                ValidBitString_subrange(s1@, start_new1, start_new1 + 1);
                // s1@.subrange(start_new1, n1) == seq![c1].concat(s1@.subrange(start_old1, n1))
                Str2Int_concat(seq![c1], s1@.subrange(start_old1, n1 as int));
                // deduce numeric relation for s1
                assert(Str2Int(s1@.subrange(start_new1, n1 as int)) ==
                       Exp_int(2, i) * Str2Int(seq![c1]) + Str2Int(s1@.subrange(start_old1, n1 as int)));
                Str2Int_singleton(c1);
                assert(Str2Int(seq![c1]) == (if c1 == '1' { 1 } else { 0 }));
                assert(b1 == (if c1 == '1' { 1 } else { 0 }));
                assert(Str2Int(s1@.subrange(start_new1, n1 as int)) == b1 * Exp_int(2, i) + Str2Int(s1@.subrange(start_old1, n1 as int)));
            } else {
                // i >= n1: subrange start stays 0, and b1 == 0
                assert(b1 == 0);
                assert(Str2Int(s1@.subrange(0, n1 as int)) == Str2Int(s1@.subrange(0, n1 as int)));
            }

            if i < n2 {
                let start_old2 = n2 as int - i as int;
                let start_new2 = start_old2 - 1;
                let c2 = s2[n2_usize - 1 - (i as usize)];
                ValidBitString_subrange(s2@, start_new2, start_new2 + 1);
                Str2Int_concat(seq![c2], s2@.subrange(start_old2, n2 as int));
                assert(Str2Int(s2@.subrange(start_new2, n2 as int)) ==
                       Exp_int(2, i) * Str2Int(seq![c2]) + Str2Int(s2@.subrange(start_old2, n2 as int)));
                Str2Int_singleton(c2);
                assert(Str2Int(seq![c2]) == (if c2 == '1' { 1 } else { 0 }));
                assert(b2 == (if c2 == '1' { 1 } else { 0 }));
                assert(Str2Int(s2@.subrange(start_new2, n2 as int)) == b2 * Exp_int(2, i) + Str2Int(s2@.subrange(start_old2, n2 as int)));
            } else {
                assert(b2 == 0);
                assert(Str2Int(s2@.subrange(0, n2 as int)) == Str2Int(s2@.subrange(0, n2 as int)));
            }

            // Combine: compute new RHS (for i+1)
            // Let A_old = Str2Int(s1@.subrange(if i<=n1 then n1-i else 0, n1))
            // Let A_new = Str2Int(s1@.subrange(if i+1<=n1 then n1-(i+1) else 0, n1))
            // Using the above equalities, A_new + B_new = A_old + B_old + (b1 + b2) * 2^i
            let lhs_old = Str2Int(s1@.subrange(if i as int <= n1 as int { n1 as int - i as int } else { 0 }, n1 as int))
                        + Str2Int(s2@.subrange(if i as int <= n2 as int { n2 as int - i as int } else { 0 }, n2 as int));
            let lhs_new = Str2Int(s1@.subrange(if (i + 1) as int <= n1 as int { n1 as int - (i + 1) as int } else { 0 }, n1 as int))
                        + Str2Int(s2@.subrange(if (i + 1) as int <= n2 as int { n2 as int - (i + 1) as int } else { 0 }, n2 as int));
            // From the cases above we can assert:
            assert(lhs_new == lhs_old + (b1 + b2) * Exp_int(2, i));

            // Now combine with the arithmetic decomposition of sum:
            // ValueLSB(temp) + new_carry * 2^{i+1} == ValueLSB(old_temp) + (bit_val + 2*new_carry) * 2^{i}
            // and (bit_val + 2*new_carry) == (b1 + b2 + carry)
            // hence ValueLSB(temp) + new_carry * 2^{i+1} == lhs_old + (b1 + b2) * 2^{i} == lhs_new
            assert(ValueLSB(temp@) + new_carry * Exp_int(2, i + 1) == lhs_new);
        }

        carry = new_carry;
        i = i + 1;
    }

    // After loop: ValueLSB(temp) + carry * 2^{len} == Str2Int(s1@) + Str2Int(s2@)
    if carry == 1 {
        let old_temp2 = temp.clone();
        temp.push('1');
        proof {
            ValueLSB_concat_prefix(old_temp2@, '1');
            ()
        }
    } else {
// </vc-code>

fn main() {}
}