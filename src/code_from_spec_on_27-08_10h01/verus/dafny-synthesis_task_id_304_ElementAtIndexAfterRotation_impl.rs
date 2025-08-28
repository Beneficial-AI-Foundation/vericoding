use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn mod_pos(a: int, b: int) -> int
    recommends b > 0
{
    ((a % b) + b) % b
}

proof fn mod_pos_properties(a: int, b: int)
    requires b > 0
    ensures 
        0 <= mod_pos(a, b) < b,
        mod_pos(a, b) == ((a % b) + b) % b
{
}

proof fn seq_index_properties<T>(s: Seq<T>, i: int)
    requires 
        s.len() > 0,
        0 <= i < s.len()
    ensures s[i] == s[i]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
proof fn element_at_index_after_rotation(l: Seq<int>, n: int, index: int) -> (element: int)
    requires 
        n >= 0,
        0 <= index < l.len(),
    ensures 
        element == l[((index - n + l.len() as int) % l.len() as int) as int],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let len = l.len() as int;
    let adjusted_index = (index - n + len) % len;
    
    l[adjusted_index]
}
// </vc-code>

fn main() {
}

}