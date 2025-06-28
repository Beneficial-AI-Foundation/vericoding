use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn nitness(b: nat, n: nat) -> bool
    requires valid_base(b)
{
    n < b
}

spec fn valid_base(b: nat) -> bool {
    b >= 2
}

spec fn is_max_nit(b: nat, q: nat) -> bool
    requires valid_base(b)
{
    q == b - 1
}

spec fn bibble(b: nat, a: Seq<nat>) -> bool {
    valid_base(b) && 
    a.len() == 4 && 
    forall|i: int| 0 <= i < a.len() ==> nitness(b, a[i])
}

// Helper function to check if a base is valid
fn check_valid_base(b: u32) -> (result: bool)
    ensures result == valid_base(b as nat)
{
    b >= 2
}

// Helper function to check nitness for concrete values
fn check_nitness(b: u32, n: u32) -> (result: bool)
    requires valid_base(b as nat)
    ensures result == nitness(b as nat, n as nat)
{
    n < b
}

// Helper function to check if q is the maximum nit for base b
fn check_is_max_nit(b: u32, q: u32) -> (result: bool)
    requires valid_base(b as nat)
    ensures result == is_max_nit(b as nat, q as nat)
{
    q == b - 1
}

// Additional helper function to check bibble property for concrete sequences
fn check_bibble(b: u32, a: [u32; 4]) -> (result: bool)
    requires valid_base(b as nat)
    ensures result == bibble(b as nat, seq![a[0] as nat, a[1] as nat, a[2] as nat, a[3] as nat])
{
    // Check all elements satisfy nitness
    let mut all_valid = true;
    let mut idx = 0;
    
    while idx < 4
        invariant 
            0 <= idx <= 4,
            valid_base(b as nat),
            all_valid ==> (forall|i: int| 0 <= i < idx ==> nitness(b as nat, a[i] as nat)),
            !all_valid ==> (exists|i: int| 0 <= i < idx && !nitness(b as nat, a[i] as nat))
    {
        if !check_nitness(b, a[idx]) {
            all_valid = false;
            proof {
                assert(!nitness(b as nat, a[idx] as nat));
            }
            break;
        }
        proof {
            assert(nitness(b as nat, a[idx] as nat));
        }
        idx += 1;
    }
    
    // After the loop, establish the connection with bibble
    proof {
        let result_seq = seq![a[0] as nat, a[1] as nat, a[2] as nat, a[3] as nat];
        
        if all_valid {
            // All elements passed the nitness check
            assert(forall|i: int| 0 <= i < 4 ==> nitness(b as nat, a[i] as nat));
            
            // Show that the sequence matches our array
            assert(result_seq[0] == a[0] as nat);
            assert(result_seq[1] == a[1] as nat);
            assert(result_seq[2] == a[2] as nat);
            assert(result_seq[3] == a[3] as nat);
            assert(result_seq.len() == 4);
            
            // Therefore all elements in the sequence satisfy nitness
            assert(forall|i: int| 0 <= i < result_seq.len() ==> nitness(b as nat, result_seq[i]));
            
            // This means bibble is satisfied
            assert(bibble(b as nat, result_seq));
        } else {
            // At least one element failed nitness check
            assert(exists|i: int| 0 <= i < 4 && !nitness(b as nat, a[i] as nat));
            assert(!forall|i: int| 0 <= i < result_seq.len() ==> nitness(b as nat, result_seq[i]));
            assert(!bibble(b as nat, result_seq));
        }
    }
    
    all_valid
}

}