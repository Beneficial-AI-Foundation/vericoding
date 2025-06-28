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
        assert(x + y < b + b);
    };
    
    assert(carry <= 1) by {
        assert(sum < 2 * b);
        assert(sum / b < 2);
        assert(sum / b <= 1);
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
        assert(c + x + y <= 1 + (b - 1) + (b - 1));
        assert(c + x + y <= 2 * b - 1);
    };
    
    assert(carry <= 1) by {
        assert(sum <= 2 * b - 1);
        assert(sum < 2 * b);
        assert(sum / b < 2);
        assert(sum / b <= 1);
    };
    
    assert(carry < b) by {
        assert(carry <= 1);
        assert(b >= 2);
        assert(1 < b);
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
        // Strengthen assertions about array bounds and properties
        assert(bibble(b, p) && bibble(b, q));
        assert(p.len() == 4 && q.len() == 4);
        assert(0 <= i < 4);
        assert(i < p.len() && i < q.len());
        
        // Prove nitness properties more explicitly
        assert(nitness(b, p[i as int])) by {
            assert(bibble(b, p) ==> (valid_base(b) && p.len() == 4 && 
                   forall|k: int| 0 <= k < p.len() ==> nitness(b, p[k])));
            assert(0 <= i < p.len());
        };
        
        assert(nitness(b, q[i as int])) by {
            assert(bibble(b, q) ==> (valid_base(b) && q.len() == 4 && 
                   forall|k: int| 0 <= k < q.len() ==> nitness(b, q[k])));
            assert(0 <= i < q.len());
        };
        
        let (digit, new_carry) = nit_add_three(b, carry, p[i as int], q[i as int]);
        result = result.push(digit);
        carry = new_carry;
        i = i + 1;
        
        // Help prove the loop invariant
        assert(nitness(b, digit));
        assert(result.len() == i);
        assert(forall|j: int| 0 <= j < i ==> nitness(b, result[j])) by {
            assert(forall|j: int| 0 <= j < i - 1 ==> nitness(b, result[j]));
            assert(nitness(b, result[(i - 1) as int]));
        };
    }
    
    // Final assertions to prove postcondition
    assert(result.len() == 4);
    assert(valid_base(b));
    assert(forall|j: int| 0 <= j < result.len() ==> nitness(b, result[j]));
    assert(bibble(b, result));
    
    result
}

fn bibble_increment(b: nat, p: Seq<nat>) -> (r: Seq<nat>)
    requires 
        bibble(b, p)
    ensures 
        bibble(b, r)
{
    let one_bibble = seq![1nat, 0nat, 0nat, 0nat];
    
    // Prove that one_bibble is a valid bibble
    assert(bibble(b, one_bibble)) by {
        assert(valid_base(b)) by {
            assert(bibble(b, p) ==> valid_base(b));
        };
        assert(one_bibble.len() == 4);
        
        // Prove nitness for each element
        assert(nitness(b, 1)) by {
            assert(valid_base(b) ==> b >= 2);
            assert(1 < b);
        };
        
        assert(nitness(b, 0)) by {
            assert(valid_base(b) ==> b >= 2);
            assert(0 < b);
        };
        
        // Prove the forall condition
        assert(forall|i: int| 0 <= i < one_bibble.len() ==> nitness(b, one_bibble[i])) by {
            assert(one_bibble.len() == 4);
            assert(one_bibble[0] == 1 && nitness(b, 1));
            assert(one_bibble[1] == 0 && nitness(b, 0));
            assert(one_bibble[2] == 0 && nitness(b, 0));
            assert(one_bibble[3] == 0 && nitness(b, 0));
        };
        
        assert(valid_base(b) && one_bibble.len() == 4 && 
               forall|i: int| 0 <= i < one_bibble.len() ==> nitness(b, one_bibble[i]));
    };
    
    bibble_add(b, p, one_bibble)
}

}