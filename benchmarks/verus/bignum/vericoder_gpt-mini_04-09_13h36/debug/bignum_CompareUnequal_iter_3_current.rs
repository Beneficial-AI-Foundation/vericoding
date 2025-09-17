use vstd::prelude::*;

verus! {

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
spec fn pow2(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * pow2(n - 1) }
}

proof fn pow2_succ(n: nat)
  ensures pow2(n + 1) == 2 * pow2(n)
  decreases n
{
    if n == 0 {
        // pow2(1) == 2 * pow2(0)
    } else {
        pow2_succ(n - 1);
    }
}

proof fn pow2_nondec(m: nat, n: nat)
  requires m >= n
  ensures pow2(m) >= pow2(n)
  decreases m
{
    if m == n {
        // pow2(m) >= pow2(n) trivially
    } else {
        // m > n, so m >= 1
        pow2_nondec(m - 1, n);
        pow2_succ(m - 1);
        // pow2(m) == 2 * pow2(m-1) >= pow2(m-1) and pow2(m-1) >= pow2(n)
        assert(2 * pow2(m - 1) >= pow2(m - 1));
        assert(pow2(m) == 2 * pow2(m - 1));
        assert(pow2(m - 1) >= pow2(n));
        assert(pow2(m) >= pow2(n));
    }
}

proof fn Str2Int_le_pow2_minus1(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s) <= pow2(s.len()) - 1
  decreases s.len()
{
    if s.len() == 0 {
        // Str2Int([]) == 0 and pow2(0)-1 == 0
    } else {
        // let prefix be all but last character
        let prefix = s.subrange(0, s.len() as int - 1);
        Str2Int_le_pow2_minus1(prefix);
        // Str2Int(s) = 2 * Str2Int(prefix) + bit_last, where bit_last is 0 or 1
        // So Str2Int(s) <= 2 * (pow2(prefix.len()) - 1) + 1 = 2 * pow2(prefix.len()) - 1
        // And pow2(s.len()) == 2 * pow2(prefix.len())
        pow2_succ(prefix.len());
        assert(Str2Int(s) <= 2 * (pow2(prefix.len()) - 1) + 1);
        assert(2 * (pow2(prefix.len()) - 1) + 1 == 2 * pow2(prefix.len()) - 1);
        assert(2 * pow2(prefix.len()) == pow2(s.len()));
        assert(Str2Int(s) <= pow2(s.len()) - 1);
    }
}

proof fn Str2Int_bit_ge(s: Seq<char>, i: nat)
  requires ValidBitString(s)
  requires i < s.len()
  requires s@[i] == '1'
  ensures Str2Int(s) >= pow2(s.len() - 1 - i)
  decreases s.len()
{
    if s.len() == 1 {
        // then i == 0 and s == ['1']
        assert(i == 0);
        // Str2Int(['1']) == 1 and pow2(0) == 1
        assert(Str2Int(s) >= 1);
        assert(pow2(s.len() - 1 - i) == pow2(0));
    } else {
        let last_idx: nat = s.len() - 1;
        if i == last_idx {
            // bit is least significant bit => contributes 1
            // so Str2Int(s) >= 1 == pow2(0)
            assert(pow2(0) == 1);
        } else {
            let prefix = s.subrange(0, s.len() as int - 1);
            // prefix has same bit at i
            Str2Int_bit_ge(prefix, i);
            // Str2Int(s) = 2 * Str2Int(prefix) + last_bit >= 2 * pow2(prefix.len() - 1 - i) = pow2(s.len() - 1 - i)
            pow2_succ(prefix.len() - 1);
            // Show 2 * pow2(prefix.len() - 1 - i) == pow2(s.len() - 1 - i)
            // More directly, from Str2Int_bit_ge(prefix, i) we have Str2Int(prefix) >= pow2(prefix.len() - 1 - i)
            assert(2 * Str2Int(prefix) >= 2 * pow2(prefix.len() - 1 - i));
            assert(Str2Int(s) >= 2 * Str2Int(prefix));
            assert(Str2Int(s) >= 2 * pow2(prefix.len() - 1 - i));
            // Now relate 2 * pow2(prefix.len() - 1 - i) to pow2(s.len() - 1 - i)
            // Note: prefix.len() == s.len() - 1
            // So 2 * pow2(prefix.len() - 1 - i) == pow2(s.len() - 1 - i)
            // This follows from repeatedly applying pow2_succ, but we can rely on definition unfolding here.
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@), ValidBitString(s2@),
    s1@.len() > 0,
    (s1@.len() > 1 ==> s1@[0] != '0'),
    s2@.len() > 0,
    (s2@.len() > 1 ==> s2@[0] != '0'),
    s1@.len() > s2@.len()
  ensures (Str2Int(s1@) < Str2Int(s2@) ==> res == -1),
    (Str2Int(s1@) == Str2Int(s2@) ==> res == 0),
    (Str2Int(s1@) > Str2Int(s2@) ==> res == 1)
// </vc-spec>
// <vc-code>
{
    // We will show Str2Int(s1@) > Str2Int(s2@) under the preconditions, then return 1.
    proof {
        let a = s1@;
        let b = s2@;
        // lengths
        let la: nat = a.len();
        let lb: nat = b.len();

        // From preconditions we have la > lb and lb > 0, so la >= 2
        assert(la > lb);
        assert(lb > 0);
        assert(la >= lb + 1);
        assert(la >= 2);

        // Because la > 1, precondition ensures a[0] != '0'. With ValidBitString, char is '0' or '1', so it must be '1'.
        assert(a@[0] != '0');
        assert(a@[0] == '1');

        // Use lemma: if a@[0] == '1' then Str2Int(a) >= pow2(la - 1)
        Str2Int_bit_ge(a, 0);

        // Use lemma: Str2Int(b) <= pow2(lb) - 1
        Str2Int_le_pow2_minus1(b);

        // From la >= lb + 1 we get la - 1 >= lb
        let m: nat = la - 1;
        assert(m >= lb);

        // pow2 is non-decreasing: pow2(m) >= pow2(lb)
        pow2_nondec(m, lb);

        // Combine inequalities:
        assert(Str2Int(a) >= pow2(m));
        assert(pow2(m) >= pow2(lb));
        // pow2(lb) > pow2(lb) - 1
        assert(pow2(lb) > pow2(lb) - 1);
        assert(pow2(lb) - 1 >= Str2Int(b));
        // From pow2(m) >= pow2(lb) and pow2(lb) - 1 >= Str2Int(b) we get Str2Int(a) > Str2Int(b)
        assert(Str2Int(a) > Str2Int(b));
    }
    return 1;
}
// </vc-code>

fn main() {}
}