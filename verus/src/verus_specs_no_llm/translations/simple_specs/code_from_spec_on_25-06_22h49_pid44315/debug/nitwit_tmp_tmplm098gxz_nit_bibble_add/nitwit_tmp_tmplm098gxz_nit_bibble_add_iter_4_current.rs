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
    n < b
}

spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) && 
    a.len() == 4 && 
    forall|i: int| 0 <= i < a.len() ==> nitness(b, a[i])
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
    
    assert(sum < 2 * b) by {
        assert(x < b);
        assert(y < b);
    };
    
    assert(z < b) by {
        assert(z == sum % b);
        assert(b > 0) by {
            assert(valid_base(b));
            assert(b >= 2);
        };
    };
    
    assert(carry < b) by {
        assert(sum < 2 * b);
        assert(carry == sum / b);
        assert(carry < 2);
        assert(b >= 2) by {
            assert(valid_base(b));
        };
    };
    
    assert(carry == 0 || carry == 1) by {
        assert(sum < 2 * b);
        assert(carry == sum / b);
        assert(carry < 2);
    };
    
    (z, carry)
}

fn nit_add_three(b: nat, c: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires valid_base(b)
    requires c == 0 || c == 1
    requires nitness(b, x)
    requires nitness(b, y)
    ensures nitness(b, z)
    ensures nitness(b, carry)
    ensures carry == 0 || carry == 1
{
    let sum = c + x + y;
    let z = sum % b;
    let carry = sum / b;
    
    assert(z < b) by {
        assert(z == sum % b);
        assert(b > 0) by {
            assert(valid_base(b));
            assert(b >= 2);
        };
    };
    
    assert(carry == 0 || carry == 1) by {
        // Since c <= 1, x < b, y < b, we have sum <= 1 + (b-1) + (b-1) = 2b - 1
        assert(sum <= 2 * b - 1) by {
            assert(c <= 1);
            assert(x <= b - 1) by {
                assert(x < b);
            };
            assert(y <= b - 1) by {
                assert(y < b);
            };
        };
        // Since sum <= 2b - 1 < 2b, we have carry = sum / b <= (2b - 1) / b < 2
        // But more precisely, since sum <= 2b - 1, carry <= 1
        assert(carry <= 1) by {
            assert(sum <= 2 * b - 1);
            assert(carry == sum / b);
        };
        assert(carry >= 0);
    };
    
    assert(carry < b) by {
        assert(carry <= 1);
        assert(b >= 2) by {
            assert(valid_base(b));
        };
    };
    
    (z, carry)
}

fn bibble_add(b: nat, p: Seq<nat>, q: Seq<nat>) -> (r: Seq<nat>)
    requires valid_base(b)
    requires bibble(b, p)
    requires bibble(b, q)
    ensures bibble(b, r)
{
    // Add corresponding positions from right to left (index 3 to 0)
    let (sum0, carry0) = nit_add(b, p[3], q[3]);
    let (sum1, carry1) = nit_add_three(b, carry0, p[2], q[2]);
    let (sum2, carry2) = nit_add_three(b, carry1, p[1], q[1]);
    let (sum3, carry3) = nit_add_three(b, carry2, p[0], q[0]);
    
    // We ignore the final carry for now (overflow)
    let result = seq![sum3, sum2, sum1, sum0];
    
    // Prove the result is a valid bibble
    assert(result.len() == 4);
    
    // Prove that each element satisfies nitness
    assert(nitness(b, result[0])) by {
        assert(result[0] == sum3);
        assert(nitness(b, sum3));
    };
    assert(nitness(b, result[1])) by {
        assert(result[1] == sum2);
        assert(nitness(b, sum2));
    };
    assert(nitness(b, result[2])) by {
        assert(result[2] == sum1);
        assert(nitness(b, sum1));
    };
    assert(nitness(b, result[3])) by {
        assert(result[3] == sum0);
        assert(nitness(b, sum0));
    };
    
    assert(forall|i: int| 0 <= i < result.len() ==> nitness(b, result[i])) by {
        assert(forall|i: int| 0 <= i < 4 ==> nitness(b, result[i])) by {
            assert(nitness(b, result[0]));
            assert(nitness(b, result[1]));
            assert(nitness(b, result[2]));
            assert(nitness(b, result[3]));
        };
    };
    
    result
}

}