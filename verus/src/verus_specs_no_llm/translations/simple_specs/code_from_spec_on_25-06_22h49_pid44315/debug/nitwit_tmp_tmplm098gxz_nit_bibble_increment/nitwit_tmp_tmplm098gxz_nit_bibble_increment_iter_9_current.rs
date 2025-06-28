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
    requires 
        valid_base(b),
        nitness(b, x),
        nitness(b, y)
    ensures 
        nitness(b, z),
        nitness(b, carry),
        carry == 0 || carry == 1,
        x + y == z + carry * b
{
    let sum = x + y;
    let z = sum % b;
    let carry = sum / b;
    
    assert(sum < 2 * b) by {
        assert(x < b && y < b);
    };
    
    assert(carry <= 1) by {
        assert(sum < 2 * b);
        assert(sum / b < 2);
    };
    
    assert(carry < b) by {
        assert(carry <= 1);
        assert(b >= 2);
    };
    
    (z, carry)
}

fn nit_add_three(b: nat, c: nat, x: nat, y: nat) -> (z: nat, carry: nat)
    requires 
        valid_base(b),
        c == 0 || c == 1,
        nitness(b, x),
        nitness(b, y)
    ensures 
        nitness(b, z),
        nitness(b, carry),
        carry == 0 || carry == 1,
        c + x + y == z + carry * b
{
    let sum = c + x + y;
    let z = sum % b;
    let carry = sum / b;
    
    assert(sum <= 2 * b - 1) by {
        assert(c <= 1 && x < b && y < b);
    };
    
    assert(carry <= 1) by {
        assert(sum <= 2 * b - 1);
        assert(sum < 2 * b);
        assert(sum / b < 2);
    };
    
    assert(carry < b) by {
        assert(carry <= 1);
        assert(b >= 2);
    };
    
    (z, carry)
}

fn bibble_add(b: nat, p: Seq<nat>, q: Seq<nat>) -> (r: Seq<nat>)
    requires 
        bibble(b, p),
        bibble(b, q)
    ensures 
        bibble(b, r)
{
    let mut result = Seq::empty();
    let mut carry = 0nat;
    let mut i = 0;
    
    while i < 4
        invariant
            0 <= i <= 4,
            result.len() == i,
            carry == 0 || carry == 1,
            valid_base(b),
            bibble(b, p),
            bibble(b, q),
            forall|j: int| 0 <= j < i ==> nitness(b, result[j])
    {
        assert(p.len() == 4 && q.len() == 4);
        assert(0 <= i < 4);
        assert(i < p.len() && i < q.len());
        
        assert(nitness(b, p[i as int]));
        assert(nitness(b, q[i as int]));
        
        let (digit, new_carry) = nit_add_three(b, carry, p[i as int], q[i as int]);
        result = result.push(digit);
        carry = new_carry;
        i = i + 1;
    }
    
    assert(result.len() == 4);
    assert(valid_base(b));
    assert(forall|j: int| 0 <= j < result.len() ==> nitness(b, result[j]));
    
    result
}

fn bibble_increment(b: nat, p: Seq<nat>) -> (r: Seq<nat>)
    requires 
        bibble(b, p)
    ensures 
        bibble(b, r)
{
    let one_bibble = seq![1nat, 0nat, 0nat, 0nat];
    
    assert(bibble(b, one_bibble)) by {
        assert(valid_base(b));
        assert(one_bibble.len() == 4);
        
        assert(nitness(b, 1)) by {
            assert(valid_base(b));
            assert(b >= 2);
            assert(1 < 2);
            assert(1 < b);
        };
        
        assert(nitness(b, 0)) by {
            assert(valid_base(b));
            assert(b >= 2);
            assert(0 < 2);
            assert(0 < b);
        };
        
        assert(forall|i: int| 0 <= i < one_bibble.len() ==> nitness(b, one_bibble[i])) by {
            assert(one_bibble[0] == 1);
            assert(one_bibble[1] == 0);
            assert(one_bibble[2] == 0);
            assert(one_bibble[3] == 0);
            assert(nitness(b, one_bibble[0]));
            assert(nitness(b, one_bibble[1]));
            assert(nitness(b, one_bibble[2]));
            assert(nitness(b, one_bibble[3]));
        };
    };
    
    bibble_add(b, p, one_bibble)
}

}