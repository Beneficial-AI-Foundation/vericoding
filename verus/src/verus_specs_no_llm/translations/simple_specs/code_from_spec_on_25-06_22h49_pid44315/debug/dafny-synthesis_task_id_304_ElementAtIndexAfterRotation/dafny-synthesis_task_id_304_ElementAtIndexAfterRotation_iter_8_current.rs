use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn ElementAtIndexAfterRotation(l: Seq<int>, n: int, index: int) -> int
    requires
        n >= 0,
        0 <= index < l.len(),
        l.len() > 0
{
    let len = l.len() as int;
    let adjusted_index = (index - n % len + len) % len;
    l.spec_index(adjusted_index)
}

// Helper lemma for modulo properties
proof fn mod_range(a: int, b: int)
    requires b > 0
    ensures 
        a % b >= 0,
        a % b < b
{
    // Built-in modulo properties are automatically handled by Verus
}

}