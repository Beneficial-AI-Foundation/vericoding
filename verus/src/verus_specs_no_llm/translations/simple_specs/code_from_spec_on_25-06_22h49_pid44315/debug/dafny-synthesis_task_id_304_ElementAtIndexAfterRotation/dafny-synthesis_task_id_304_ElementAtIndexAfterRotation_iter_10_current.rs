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
    recommends
        {
            let len = l.len() as int;
            let rotation_offset = n % len;
            let adjusted_index = if index >= rotation_offset {
                index - rotation_offset
            } else {
                index - rotation_offset + len
            };
            0 <= adjusted_index < len
        }
{
    let len = l.len() as int;
    let rotation_offset = n % len;
    let adjusted_index = if index >= rotation_offset {
        index - rotation_offset
    } else {
        index - rotation_offset + len
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
    // Built-in modulo properties are automatically handled by Verus
}

// Additional helper lemma to prove bounds for the adjusted index
proof fn adjusted_index_bounds(l: Seq<int>, n: int, index: int)
    requires
        n >= 0,
        0 <= index < l.len(),
        l.len() > 0
    ensures
        {
            let len = l.len() as int;
            let rotation_offset = n % len;
            let adjusted_index = if index >= rotation_offset {
                index - rotation_offset
            } else {
                index - rotation_offset + len
            };
            0 <= adjusted_index < len
        }
{
    let len = l.len() as int;
    mod_range(n, len);
    let rotation_offset = n % len;
    
    // Prove that rotation_offset is in valid range
    assert(0 <= rotation_offset < len);
    
    if index >= rotation_offset {
        let adjusted_index = index - rotation_offset;
        assert(adjusted_index >= 0);
        assert(adjusted_index < len);
    } else {
        let adjusted_index = index - rotation_offset + len;
        assert(adjusted_index >= 0) by {
            assert(index >= 0);
            assert(rotation_offset <= len);
        };
        assert(adjusted_index < len) by {
            assert(index < len);
            assert(rotation_offset > 0);
        };
    }
}

}