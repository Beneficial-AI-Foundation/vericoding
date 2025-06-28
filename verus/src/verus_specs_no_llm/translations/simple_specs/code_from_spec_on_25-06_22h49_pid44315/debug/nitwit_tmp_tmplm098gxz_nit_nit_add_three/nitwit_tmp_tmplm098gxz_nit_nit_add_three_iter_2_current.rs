use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn valid_base(b: nat) -> bool {
    b >= 2
}

spec fn nitness(b: nat, n: nat) -> bool
    requires valid_base(b)
{
    0 <= n < b
}

fn nit_add(b: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires valid_base(b)
    requires nitness(b, x)
    requires nitness(b, y)
    ensures nitness(b, z)
    ensures nitness(b, carry)
    ensures carry == 0 || carry == 1
{
    let sum = x + y;
    let z = sum % b;
    let carry = sum / b;
    
    // Prove properties step by step
    assert(x < b);
    assert(y < b);
    assert(sum < b + b);
    assert(sum < 2 * b);
    
    // Use Verus division properties
    assert(sum == carry * b + z) by {
        assert(sum / b == carry);
        assert(sum % b == z);
    };
    
    // Since sum < 2*b, carry must be 0 or 1
    assert(carry * b <= sum);
    assert(sum < 2 * b);
    assert(carry < 2);
    assert(carry >= 0);
    
    // z is remainder, so z < b
    assert(z < b);
    assert(z >= 0);
    
    (z, carry)
}

fn nit_add_three(b: nat, c: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires valid_base(b)
    requires nitness(b, x)
    requires nitness(b, y)
    requires c == 0 || c == 1
    ensures nitness(b, z)
    ensures nitness(b, carry)
    ensures carry == 0 || carry == 1
{
    let sum = c + x + y;
    let z = sum % b;
    let carry = sum / b;
    
    // Prove properties step by step
    assert(x < b);
    assert(y < b);
    assert(c <= 1);
    assert(sum <= 1 + (b - 1) + (b - 1)) by {
        assert(c <= 1);
        assert(x <= b - 1);
        assert(y <= b - 1);
    };
    assert(sum <= 2 * b - 1);
    assert(sum < 2 * b);
    
    // Use division properties
    assert(sum == carry * b + z) by {
        assert(sum / b == carry);
        assert(sum % b == z);
    };
    
    // Since sum < 2*b, carry must be 0 or 1
    assert(carry * b <= sum);
    assert(sum < 2 * b);
    assert(carry < 2);
    assert(carry >= 0);
    
    // z is remainder, so z < b
    assert(z < b);
    assert(z >= 0);
    
    (z, carry)
}

}