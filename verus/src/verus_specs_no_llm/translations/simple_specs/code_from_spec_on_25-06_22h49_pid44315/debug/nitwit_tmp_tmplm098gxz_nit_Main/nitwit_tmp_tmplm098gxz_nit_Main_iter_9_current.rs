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
    let result_seq = seq![a[0] as nat, a[1] as nat, a[2] as nat, a[3] as nat];
    
    // Check each element individually
    let check0 = check_nitness(b, a[0]);
    let check1 = check_nitness(b, a[1]);
    let check2 = check_nitness(b, a[2]);
    let check3 = check_nitness(b, a[3]);
    
    let all_valid = check0 && check1 && check2 && check3;
    
    proof {
        // First establish basic properties of result_seq
        assert(result_seq.len() == 4);
        assert(result_seq[0] == a[0] as nat);
        assert(result_seq[1] == a[1] as nat);
        assert(result_seq[2] == a[2] as nat);
        assert(result_seq[3] == a[3] as nat);
        
        // Establish the connection between individual checks and the forall property
        if all_valid {
            assert(nitness(b as nat, a[0] as nat));
            assert(nitness(b as nat, a[1] as nat));
            assert(nitness(b as nat, a[2] as nat));
            assert(nitness(b as nat, a[3] as nat));
            
            // Prove the forall property
            assert forall|i: int| 0 <= i < result_seq.len() implies nitness(b as nat, result_seq[i]) by {
                assert(0 <= i < 4);
                if i == 0 {
                    assert(result_seq[i] == a[0] as nat);
                    assert(nitness(b as nat, result_seq[i]));
                } else if i == 1 {
                    assert(result_seq[i] == a[1] as nat);
                    assert(nitness(b as nat, result_seq[i]));
                } else if i == 2 {
                    assert(result_seq[i] == a[2] as nat);
                    assert(nitness(b as nat, result_seq[i]));
                } else {
                    assert(i == 3);
                    assert(result_seq[i] == a[3] as nat);
                    assert(nitness(b as nat, result_seq[i]));
                }
            };
            
            // Therefore bibble is satisfied
            assert(valid_base(b as nat));
            assert(result_seq.len() == 4);
            assert(forall|i: int| 0 <= i < result_seq.len() ==> nitness(b as nat, result_seq[i]));
            assert(bibble(b as nat, result_seq));
        } else {
            // At least one element failed nitness check
            // We need to show that bibble is false
            if !check0 {
                assert(!nitness(b as nat, a[0] as nat));
                assert(!nitness(b as nat, result_seq[0]));
                assert(exists|i: int| 0 <= i < result_seq.len() && !nitness(b as nat, result_seq[i]));
            } else if !check1 {
                assert(!nitness(b as nat, a[1] as nat));
                assert(!nitness(b as nat, result_seq[1]));
                assert(exists|i: int| 0 <= i < result_seq.len() && !nitness(b as nat, result_seq[i]));
            } else if !check2 {
                assert(!nitness(b as nat, a[2] as nat));
                assert(!nitness(b as nat, result_seq[2]));
                assert(exists|i: int| 0 <= i < result_seq.len() && !nitness(b as nat, result_seq[i]));
            } else {
                assert(!check3);
                assert(!nitness(b as nat, a[3] as nat));
                assert(!nitness(b as nat, result_seq[3]));
                assert(exists|i: int| 0 <= i < result_seq.len() && !nitness(b as nat, result_seq[i]));
            }
            assert(!forall|i: int| 0 <= i < result_seq.len() ==> nitness(b as nat, result_seq[i]));
            assert(!bibble(b as nat, result_seq));
        }
    }
    
    all_valid
}

}