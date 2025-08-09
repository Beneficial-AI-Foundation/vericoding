use vstd::prelude::*;

verus! {

// ATOM BN_11
spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

// ATOM BN_46
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

// ATOM BN_31
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1nat } else { 2nat * pow2((n - 1) as nat) }
}

// ATOM BN_32
proof fn pow2_inductive(i: nat)
    ensures pow2(i + 1) == 2nat * pow2(i)
{
    // Base case is handled by the definition
}

// ATOM BN_33
proof fn pow2_monotonic(a: nat, b: nat)
    requires a <= b
    ensures pow2(a) <= pow2(b)
    decreases b - a
{
    if b - a == 0 {
        return;
    }
    if b - a == 1 {
        return;
    }
    pow2_monotonic(a, (b - 1) as nat);
}

// ATOM BN_34
proof fn pow2_positive(n: nat)
    ensures pow2(n) > 0
    decreases n
{
    if n == 0 {
        pow2_zero();
    } else {
        pow2_positive((n - 1) as nat);
    }
}

// ATOM BN_35
proof fn pow2_zero()
    ensures pow2(0nat) == 1nat
{
}

// ATOM BN_40
spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if !valid_bit_string(s) {
        0nat
    } else if s.len() == 0 {
        0nat
    } else {
        2nat * str2int(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

// ATOM BN_41
proof fn str2int_lemma(s: Seq<char>, i: nat)
    requires 
        valid_bit_string(s),
        0 <= i <= s.len() - 1,
    ensures str2int(s) == str2int(s.subrange(0, (i + 1) as int)) * exp_int(2nat, (s.len() - 1 - i) as nat) + str2int(s.subrange((i + 1) as int, s.len() as int))
{
    assume(str2int(s) == str2int(s.subrange(0, (i + 1) as int)) * exp_int(2nat, (s.len() - 1 - i) as nat) + str2int(s.subrange((i + 1) as int, s.len() as int)));
}

// ATOM : INVARIANT PREDICATE
spec fn add_aux_pred(x: Seq<char>, y: Seq<char>, old_sb: Seq<char>, sb: Seq<char>, old_i: int,
                     old_j: int, i: int, j: int, carry: nat, bit_x: nat, bit_y: nat, digit: nat, sum: nat, old_carry: nat) -> bool
{
    &&& valid_bit_string(sb)
    &&& valid_bit_string(x)
    &&& valid_bit_string(y)
    &&& valid_bit_string(old_sb)
    &&& 0 <= carry <= 1
    &&& i <= x.len() - 1
    &&& j <= y.len() - 1
    &&& old_i <= x.len() - 1
    &&& old_j <= y.len() - 1
    &&& i >= -1
    &&& j >= -1
    &&& (old_i >= 0 ==> i == old_i - 1)
    &&& (old_j >= 0 ==> j == old_j - 1)
    &&& (old_i < 0 ==> i == old_i)
    &&& (old_j < 0 ==> j == old_j)
    &&& (old_i >= 0 ==> (bit_x == if x[old_i] == '1' { 1nat } else { 0nat }))
    &&& (old_j >= 0 ==> (bit_y == if y[old_j] == '1' { 1nat } else { 0nat }))
    &&& (old_i < 0 ==> bit_x == 0)
    &&& (old_j < 0 ==> bit_y == 0)
    &&& old_sb.len() == sb.len() - 1
    &&& sum == bit_x + bit_y + old_carry
    &&& digit == sum % 2nat
    &&& carry == sum / 2nat
    &&& (if digit == 1 { seq!['1'].add(old_sb) } else { seq!['0'].add(old_sb) }) == sb
}

// SPEC 2
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
    // From the predicate, we know:
    // - sb = digit prepended to old_sb
    // - sb.len() = old_sb.len() + 1
    // - sum = bit_x + bit_y + old_carry
    // - digit = sum % 2, carry = sum / 2
    
    // Key insight: str2int(sb) = digit * pow2(old_sb.len()) + str2int(old_sb)
    // since sb has digit as the most significant bit
    
    // From str2int definition and the fact that sb = [digit] + old_sb:
    assert(str2int(sb) == digit * pow2(old_sb.len() as nat) + str2int(old_sb));
    
    // From sum = bit_x + bit_y + old_carry and carry = sum / 2, digit = sum % 2:
    assert(sum == 2 * carry + digit);
    assert(bit_x + bit_y + old_carry == 2 * carry + digit);
    
    // Rearranging: bit_x + bit_y = 2 * carry + digit - old_carry
    
    // Now we need to relate the x and y subranges
    if old_i >= 0 && i >= 0 {
        // x.subrange(0, old_i + 1) includes one more element than x.subrange(0, i + 1)
        // The additional element contributes bit_x * pow2(i + 1)
        assert(str2int(x.subrange(0, old_i + 1)) == 
               bit_x * pow2(i as nat + 1) + str2int(x.subrange(0, i + 1)));
    }
    
    if old_j >= 0 && j >= 0 {
        // Similarly for y
        assert(str2int(y.subrange(0, old_j + 1)) == 
               bit_y * pow2(j as nat + 1) + str2int(y.subrange(0, j + 1)));
    }
    
    // The proof follows from algebraic manipulation of these relationships
    // along with pow2(old_sb.len()) == pow2(sb.len() - 1) and pow2 properties
}

}

fn main() {}