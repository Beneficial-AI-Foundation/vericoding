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

}