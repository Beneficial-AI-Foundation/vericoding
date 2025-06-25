// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Allow42(x: int, y: int) -> z: int, err: bool
    ensures y != 42 ==> z == x/(42-y) and err == false;,
            y == 42 ==> z == 0 and err == true;
{
}

}