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
proof fn lemma_div2_identity(n: nat)
    ensures n == 2 * (n / 2) + (n % 2)
{
    assert(n == 2 * (n / 2) + (n % 2));
}

spec fn Nat2Bits(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let q = n / 2;
        let r = n % 2;
        Nat2Bits(q) + seq![if r == 1 { '1' } else { '0' }]
    }
}

proof fn lemma_nat2bits_valid(n: nat)
    ensures ValidBitString(Nat2Bits(n))
    decreases n
{
    if n == 0 {
        assert(ValidBitString(Seq::<char>::empty()));
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_nat2bits_valid(q);
        let s1 = Nat2Bits(q);
        let last = if r == 1 { '1' } else { '0' };
        let s = s1 + seq![last];
        assert(s.len() == s1.len() + 1);
        assert(forall |i: int|
            0 <= i && i < s.len() as int ==> (#[trigger] s.index(i) == '0' || #[trigger] s.index(i) == '1')
        ) by {
            assert(s.len() == s1.len() + 1);
            assert forall |i: int| 0 <= i && i < s.len() as int implies s.index(i) == '0' || s.index(i) == '1' by {
                if i < s1.len() as int {
                    assert((s1 + seq![last]).index(i) == s1.index(i));
                    assert(0 <= i && i < s1.len() as int);
                    assert(ValidBitString(s1));
                } else {
                    assert(i == s1.len() as int);
                    assert((s1 + seq![last]).index(i) == last);
                    if r == 1 {
                        assert(last == '1');
                    } else {
                        assert(last == '0');
                    }
                }
            }
        }
    }
}

proof fn lemma_str2int_nat2bits(n: nat)
    ensures Str2Int(Nat2Bits(n)) == n
    decreases n
{
    if n == 0 {
        assert(Nat2Bits(0) == Seq::<char>::empty());
        assert(Str2Int(Seq::<char>::empty()) == 0);
    } else {
        let q = n / 2;
        let r = n % 2;
        lemma_str2int_nat2bits(q);
        lemma_nat2bits_valid(q);
        let s1 = Nat2Bits(q);
        let last = if r == 1 { '1' } else { '0' };
        let s = s1 + seq![last];
        assert(Nat2Bits(n) == s1 + seq![if r == 1 { '1' } else { '0' }]);
        assert(Nat2Bits(n) == s);

        lemma_nat2bits_valid(n);
        assert(ValidBitString(Nat2Bits(n)));

        assert(s.len() == s1.len() + 1);
        assert(s.subrange(0, s.len() as int - 1) == s1) by {
            assert(s.len() as int - 1 == s1.len() as int);
            assert((s1 + seq![last]).subrange(0, s1.len() as int) == s1);
        }
        assert(s.index(s.len() as int - 1) == last) by {
            assert(s.len() == s1.len() + 1);
            assert((s1 + seq![last]).index(s1.len() as int) == last);
            assert(s.len() as int - 1 == s1.len() as int);
        }

        assert(Str2Int(s) ==
            2 * Str2Int(s.subrange(0, s.len() as int - 1))
            + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
        );

        assert(Str2Int(s) == 2 * Str2Int(s1) + (if last == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s1) == q);

        assert(0nat <= r && r < 2nat);
        if r == 1 {
            assert(last == '1');
            assert((if last == '1' { 1nat } else { 0nat }) == 1nat);
            assert(Str2Int(s) == 2 * q + 1);
        } else {
            assert(r == 0);
            assert(last == '0');
            assert((if last == '1' { 1nat } else { 0nat }) == 0nat);
            assert(Str2Int(s) == 2 * q);
        }

        lemma_div2_identity(n);
        assert(2 * q + r == n);
        assert(Str2Int(Nat2Bits(n)) == n);
    }
}

proof fn lemma_subrange_extends_by_index(s: Seq<char>, i: nat)
    requires i < s.len()
    ensures s.subrange(0, i as int) + seq![s.index(i as int)] == s.subrange(0, (i + 1) as int)
{
    let left = s.subrange(0, i as int) + seq![s.index(i as int)];
    let right = s.subrange(0, (i + 1) as int);
    assert(left.len() == i + 1);
    assert(right.len() == i + 1);
    assert(forall |j: int|
        0 <= j && j < left.len() as int ==> #[trigger] left.index(j) == #[trigger] right.index(j)
    ) by {
        assert forall |j: int| 0 <= j && j < left.len() as int implies left.index(j) == right.index(j) by {
            assert(0 <= j && j < (i + 1) as int);
            if j < i as int {
                assert((s.subrange(0, i as int) + seq![s.index(i as int)]).index(j) == s.subrange(0, i as int).index(j));
                assert(s.subrange(0, (i + 1) as int).index(j) == s.index(j));
                assert(s.subrange(0, i as int).index(j) == s.index(j));
            } else {
                assert(j == i as int);
                assert((s.subrange(0, i as int) + seq![s.index(i as int)]).index(j) == seq![s.index(i as int)].index(0));
                assert(seq![s.index(i as int)].index(0) == s.index(i as int));
                assert(s.subrange(0, (i + 1) as int).index(j) == s.index(j));
                assert(j == i as int);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let n = Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@);
    let bits = Nat2Bits(n);
    let mut res: Vec<char> = Vec::new();
    let mut i: nat = 0;
    while i < bits.len()
        invariant
            i <= bits.len(),
            res@ == bits.subrange(0, i as int)
        decreases (bits.len() - i)
    {
        let i_old = i;
        let c = bits.index(i_old as int);
        let old_res = res@;
        res.push(c);
        proof {
            assert(res@ == old_res + seq![c]);
            lemma_subrange_extends_by_index(bits, i_old);
            assert(res@ == bits.subrange(0, (i_old + 1) as int));
        }
        i = i_old + 1;
        assert(res@ == bits.subrange(0, i as int));
        assert(i <= bits.len());
    }
    proof {
        assert(res@ == bits.subrange(0, bits.len() as int));
        assert(bits.subrange(0, bits.len() as int) == bits);
        lemma_nat2bits_valid(n);
        lemma_str2int_nat2bits(n);
        assert(ValidBitString(bits));
        assert(ValidBitString(res@));
        assert(Str2Int(res@) == n);
    }
    res
}
// </vc-code>

fn main() {}
}