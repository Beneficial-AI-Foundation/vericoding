use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn mod_properties(a: int, b: int)
    requires
        b > 0,
    ensures
        -b < a % b <= 0 || 0 <= a % b < b,
        (a + b) % b == a % b,
{
}

proof fn modulo_rotation_property(l: Seq<int>, n: int, i: int)
    requires
        n >= 0 && n < l.len(),
        i >= 0 && i < l.len(),
    ensures
        (i + n) % l.len() >= 0,
        (i + n) % l.len() < l.len(),
        ((i + n) as nat % l.len()) as int == (i + n) % l.len(),
{
    let len = l.len() as int;
    mod_properties(i + n, len);
    assert(0 <= (i + n) % len < len);
}

proof fn modulo_property_for_index(n: int, len: int, j: int)
    requires
        n >= 0 && n < len,
        j >= 0 && j < len,
    ensures
        (j + n) % len >= 0,
        (j + n) % len < len,
{
    mod_properties(j + n, len);
    assert(0 <= (j + n) % len < len);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn split_and_append(l: Seq<int>, n: int) -> (r: Seq<int>)
    requires 
        n >= 0 && n < l.len(),
    ensures 
        r.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> r[i] == l[((i + n) as nat % l.len()) as int],
// </vc-spec>
// <vc-code>
{
    let len_int = l.len() as int;
    let mut result = Seq::<int>::empty();
    let mut j: int = 0;
    
    proof { assert(n >= 0 && n < l.len()); }
    
    while j < len_int
        invariant
            result.len() as int == j,
            j >= 0 && j <= len_int,
            forall|k: int| 0 <= k < j ==> {
                let rotated_index = (k + n) % len_int;
                rotated_index >= 0 && rotated_index < len_int
            },
            forall|k: int| 0 <= k < j ==> {
                let rotated_index = (k + n) % len_int;
                result[k] == l.index(rotated_index as nat)
            }
    {
        let rotated_index = (j + n) % len_int;
        
        proof { 
            modulo_property_for_index(n, len_int, j);
            assert(rotated_index >= 0 && rotated_index < len_int);
            assert((rotated_index as nat) < l.len()); 
        }
        
        result = result.add(l.index(rotated_index as nat));
        j = j + 1;
    }
    
    result
}
// </vc-code>

fn main() {
}

}