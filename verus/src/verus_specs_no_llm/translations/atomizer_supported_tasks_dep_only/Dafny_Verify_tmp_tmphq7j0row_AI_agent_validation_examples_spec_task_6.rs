// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputePower1(N: int) -> (y: nat) requires N >= 0
//     ensures y == Power(N)
// {
//     y := 1;
//     var x := 0; 
//     while x != N
//         decreases N - x
//         invariant 0 <= x <= N
//         invariant y == Power(x)
//     {
//         x, y: = x + 1, y + y;
//     }
// }



// Fine_tuned davinci-003 completion: // method ComputePower1(N: int) returns (y: nat) requires N >= 0
//     ensures y == Power(N)
// {
//     y := 1;
//     var x := 0; 
//     while x != N
//         decreases N - x
//         invariant 0 <= x <= N
//         invariant y == Power(x)
//     {
//         x, y: = x + 1, y + y;
//     }
// }

// SPEC 


// Original davinci-003 completion: // method ComputePower1(N: int) returns (y: nat)
    requires
        N >= 0
//,
        N >= 0
//,
        N >= 0
//
    ensures
        y == Power(N)
//,
        y == Power(N)
//,
        y == Power(N)
//
{
    return (0, 0, 0, 0, 0);
}

}