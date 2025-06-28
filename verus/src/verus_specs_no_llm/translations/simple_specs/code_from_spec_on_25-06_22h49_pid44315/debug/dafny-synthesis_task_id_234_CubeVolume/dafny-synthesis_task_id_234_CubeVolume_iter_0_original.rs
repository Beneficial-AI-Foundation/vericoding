// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CubeVolume(size: int) -> (volume: int)
    requires
        size > 0
    ensures
        volume == size * size * size
{
    return 0;
}

}