// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
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