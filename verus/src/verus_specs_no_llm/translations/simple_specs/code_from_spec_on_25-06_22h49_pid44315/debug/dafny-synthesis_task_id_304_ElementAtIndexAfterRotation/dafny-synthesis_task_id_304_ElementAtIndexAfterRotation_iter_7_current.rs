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
    proof {
        // Prove that adjusted_index is within bounds
        assert(n % len >= 0 && n % len < len) by {
            mod_range(n, len);
        };
        assert(index - n % len + len >= 0) by {
            assert(index >= 0);
            assert(n % len < len);
        };
        assert(adjusted_index >= 0 && adjusted_index < len) by {
            mod_range(index - n % len + len, len);
        };
    };
    l.spec_index(adjusted_index)
}

// Helper lemma for modulo properties
proof fn mod_range(a: int, b: int)
    requires b > 0
    ensures 
        a % b >= 0,
        a % b < b
{
    // This is a built-in property of modulo in Verus
}

}