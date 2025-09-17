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
spec fn NatToBitSeq(n: nat) -> Seq<char>
decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        NatToBitSeq(q).push(if r == 1 { '1' } else { '0' })
    }
}

proof fn lemma_NatToBitSeq_props(n: nat)
    ensures
        ValidBitString(NatToBitSeq(n)),
        Str2Int(NatToBitSeq(n)) == n
    decreases n
{
    if n == 0 {
        // Str2Int(Seq::empty()) == 0 by definition; ValidBitString holds vacuously
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_NatToBitSeq_props(q);
        let s = NatToBitSeq(q);
        let c = if r == 1 { '1' } else { '0' };
        // ValidBitString(s.push(c))
        assert forall |i: int|
            0 <= i && i < s.push(c).len() as int
            implies (s.push(c).index(i) == '0' || s.push(c).index(i) == '1')
        by {
            assert(s.push(c).len() == s.len() + 1);
            if i == s.len() as int {
                assert(s.push(c).index(i) == c);
                if r == 1 {
                    assert(c == '1');
                } else {
                    assert(c == '0');
                }
            } else {
                assert(i < s.len() as int);
                assert(s.push(c).index(i) == s.index(i));
            }
        }

        // Str2Int(s.push(c)) = 2 * Str2Int(s) + bit(c)
        let sp = s.push(c);
        assert(sp.len() > 0);
        assert(
            Str2Int(sp)
            ==
            2 * Str2Int(sp.subrange(0, sp.len() as int - 1))
            +
            (if sp.index(sp.len() as int - 1) == '1' { 1nat } else { 0nat })
        );
        assert(sp.subrange(0, sp.len() as int - 1) == s);
        assert(sp.index(sp.len() as int - 1) == c);
        assert(Str2Int(sp) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }));

        // Use IH: Str2Int(s) == q
        assert(Str2Int(s) == q);

        // Relate (if c == '1' {1} else {0}) to r
        if r == 1 {
            assert(c == '1');
            assert((if c == '1' { 1nat } else { 0nat }) == 1nat);
        } else {
            assert(r < 2);
            assert(r != 1);
            assert((if c == '1' { 1nat } else { 0nat }) == 0nat);
            // From 0 <= r < 2 and r != 1, conclude r == 0
            assert(r <=
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
spec fn NatToBitSeq(n: nat) -> Seq<char>
decreases n
{
    if n == 0 {
        Seq::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        NatToBitSeq(q).push(if r == 1 { '1' } else { '0' })
    }
}

proof fn lemma_NatToBitSeq_props(n: nat)
    ensures
        ValidBitString(NatToBitSeq(n)),
        Str2Int(NatToBitSeq(n)) == n
    decreases n
{
    if n == 0 {
        // Str2Int(Seq::empty()) == 0 by definition; ValidBitString holds vacuously
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_NatToBitSeq_props(q);
        let s = NatToBitSeq(q);
        let c = if r == 1 { '1' } else { '0' };
        // ValidBitString(s.push(c))
        assert forall |i: int|
            0 <= i && i < s.push(c).len() as int
            implies (s.push(c).index(i) == '0' || s.push(c).index(i) == '1')
        by {
            assert(s.push(c).len() == s.len() + 1);
            if i == s.len() as int {
                assert(s.push(c).index(i) == c);
                if r == 1 {
                    assert(c == '1');
                } else {
                    assert(c == '0');
                }
            } else {
                assert(i < s.len() as int);
                assert(s.push(c).index(i) == s.index(i));
            }
        }

        // Str2Int(s.push(c)) = 2 * Str2Int(s) + bit(c)
        let sp = s.push(c);
        assert(sp.len() > 0);
        assert(
            Str2Int(sp)
            ==
            2 * Str2Int(sp.subrange(0, sp.len() as int - 1))
            +
            (if sp.index(sp.len() as int - 1) == '1' { 1nat } else { 0nat })
        );
        assert(sp.subrange(0, sp.len() as int - 1) == s);
        assert(sp.index(sp.len() as int - 1) == c);
        assert(Str2Int(sp) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat }));

        // Use IH: Str2Int(s) == q
        assert(Str2Int(s) == q);

        // Relate (if c == '1' {1} else {0}) to r
        if r == 1 {
            assert(c == '1');
            assert((if c == '1' { 1nat } else { 0nat }) == 1nat);
        } else {
            assert(r < 2);
            assert(r != 1);
            assert((if c == '1' { 1nat } else { 0nat }) == 0nat);
            // From 0 <= r < 2 and r != 1, conclude r == 0
            assert(r <=
// </vc-code>

fn main() {}
}