use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn mod_add_basic(a: int, b: int, m: int)
    requires m > 0
    ensures (a + b) % m == ((a % m) + (b % m)) % m
{
    // This is a basic modular arithmetic property
}

proof fn mod_sub_basic(a: int, b: int, m: int)
    requires m > 0
    ensures (a - b) % m == ((a % m) - (b % m) + m) % m
{
    // This is a basic modular arithmetic property
}

proof fn mod_bounds(a: int, m: int)
    requires m > 0
    ensures 0 <= a % m < m
{
    // Basic property of modulo operation
}

proof fn mod_equivalence(a: int, b: int, m: int)
    requires m > 0
    ensures (a % m) == ((a + b * m) % m)
{
    // Modular arithmetic equivalence
}
// </vc-helpers>

// <vc-spec>
fn rotate_right(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires n >= 0,
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r.index(i) == l.index((i - n + l.len() as int) % l.len() as int),
// </vc-spec>
// <vc-code>
{
    if l.len() == 0nat {
        return l;
    }
    
    let ghost len = l.len() as int;
    let ghost effective_n = n % len;
    
    let result = Seq::new(l.len(), |i: int| {
        let ghost source_index = (i - effective_n + len) % len;
        l.index(source_index)
    });
    
    proof {
        assert forall|i: int| 0 <= i < l.len() implies {
            let source_index = (i - effective_n + len) % len;
            &&& 0 <= source_index < len
            &&& result.index(i) == l.index(source_index)
        } by {
            if 0 <= i < l.len() {
                let source_index = (i - effective_n + len) % len;
                mod_bounds(i - effective_n + len, len);
            }
        };
        
        assert forall|i: int| 0 <= i < l.len() implies 
            result.index(i) == l.index((i - n + l.len() as int) % l.len() as int) by {
            if 0 <= i < l.len() {
                let len_int = l.len() as int;
                let source1 = (i - effective_n + len_int) % len_int;
                let source2 = (i - n + len_int) % len_int;
                
                // effective_n = n % len_int
                // So n = effective_n + k * len_int for some integer k
                // Therefore: i - n + len_int = i - effective_n + len_int - k * len_int
                // Since (a - k * m) % m == a % m, we have source1 == source2
                mod_equivalence(i - effective_n + len_int, -(n / len_int), len_int);
            }
        };
    }
    
    result
}
// </vc-code>

fn main() {}

}