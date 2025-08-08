use vstd::prelude::*;

verus! {

// ATOM BN_46
spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

// ATOM BN_11
spec fn exp_int(x: nat, y: nat) -> nat 
    decreases y
{
    if y == 0 { 1 } else { x * exp_int(x, (y - 1) as nat) }
}

// ATOM BN_40
spec fn str2int(s: Seq<char>) -> nat 
    decreases s.len()
{
    if s.len() == 0 { 
        0nat 
    } else { 
        2 * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

// ATOM BN_31
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

// ATOM BN_41
proof fn str2int_lemma(s: Seq<char>, i: nat)
    requires 
        valid_bit_string(s),
        0 <= i <= s.len() - 1,
    ensures 
        str2int(s) == str2int(s.subrange(0, i as int + 1)) * exp_int(2, (s.len() - 1 - i) as nat) + str2int(s.subrange(i as int + 1, s.len() as int))
{
    assume(str2int(s) == str2int(s.subrange(0, i as int + 1)) * exp_int(2, (s.len() - 1 - i) as nat) + str2int(s.subrange(i as int + 1, s.len() as int)));
}

// ATOM : INVARIANT PREDICATE
spec fn add_aux_pred(x: Seq<char>, y: Seq<char>, old_sb: Seq<char>, sb: Seq<char>, old_i: int,
                     old_j: int, i: int, j: int, carry: nat, bit_x: nat, bit_y: nat, digit: nat, sum: nat, old_carry: nat) -> bool
{
    valid_bit_string(sb) &&
    valid_bit_string(x) &&
    valid_bit_string(y) &&
    valid_bit_string(old_sb) &&
    0 <= carry <= 1 &&
    i <= x.len() - 1 && j <= y.len() - 1 &&
    old_i <= x.len() - 1 && old_j <= y.len() - 1 &&
    i >= -1 &&
    j >= -1 &&
    (old_i >= 0 ==> i == old_i - 1) &&
    (old_j >= 0 ==> j == old_j - 1) &&
    (old_i < 0 ==> i == old_i) &&
    (old_j < 0 ==> j == old_j) &&
    (old_i >= 0 ==> (bit_x == if x[old_i] == '1' { 1nat } else { 0nat })) &&
    (old_j >= 0 ==> (bit_y == if y[old_j] == '1' { 1nat } else { 0nat })) &&
    (old_i < 0 ==> bit_x == 0) &&
    (old_j < 0 ==> bit_y == 0) &&
    old_sb.len() == sb.len() - 1 &&
    sum == bit_x + bit_y + old_carry &&
    digit == sum % 2 &&
    carry == sum / 2 &&
    (if digit == 1 { seq!['1'].add(old_sb) } else { seq!['0'].add(old_sb) }) == sb
}

// ATOM BN_2
proof fn add_aux_top(x: Seq<char>, y: Seq<char>, old_sb: Seq<char>, sb: Seq<char>, old_i: int,
                     old_j: int, i: int, j: int, carry: nat, bit_x: nat, bit_y: nat, digit: nat, sum: nat, old_carry: nat)
    requires add_aux_pred(x, y, old_sb, sb, old_i, old_j, i, j, carry, bit_x, bit_y, digit, sum, old_carry)
    ensures str2int(old_sb) +
          (old_carry * pow2(old_sb.len() as nat)) +
          (if old_i >= 0 { str2int(x.subrange(0, old_i + 1)) * pow2(old_sb.len() as nat) } else { 0nat }) +
          (if old_j >= 0 { str2int(y.subrange(0, old_j + 1)) * pow2(old_sb.len() as nat) } else { 0nat }) ==
          str2int(sb) +
          (carry * pow2(sb.len() as nat)) +
          (if i >= 0 { str2int(x.subrange(0, i + 1)) * pow2(sb.len() as nat) } else { 0nat }) +
          (if j >= 0 { str2int(y.subrange(0, j + 1)) * pow2(sb.len() as nat) } else { 0nat })
{
}

}

fn main() {}