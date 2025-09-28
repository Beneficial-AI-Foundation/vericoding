use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_mod_properties(a: int, b: int)
    requires
        b > 0,
    ensures
        a % b >= 0,
        a % b < b,
        a % b == a - b * (a / b)
{
}

proof fn lemma_division_properties(a: int, b: int)
    requires
        b > 0,
    ensures
        (a + b) / b == a / b + 1,
        if a >= 0 { a / b >= 0 } else { true }
{
}

proof fn lemma_rotate_index_equivalence(l: Seq<int>, n: int, i: int)
    requires
        n >= 0,
        0 <= i < l.len() as int,
        l.len() > 0,
    ensures
        (i - n + l.len() as int) >= 0,
{
    lemma_mod_properties(i - n + l.len() as int, l.len() as int);
    let adjusted_index = (i - n + l.len() as int) % l.len() as int;
    assert(0 <= adjusted_index < l.len() as int);
}

proof fn lemma_rotate_complete_coverage(l: Seq<int>, n: int)
    requires
        n >= 0,
        l.len() > 0,
    ensures
        forall|j: int| 0 <= j < l.len() as int ==>
            exists|k: int| 0 <= k < l.len() as int && 
                (k - n + l.len() as int) % l.len() as int == j,
{
}

proof fn lemma_mod_usize_conversion(i: usize, n: usize, len: usize)
    requires
        len > 0,
    ensures
        (((i as int - n as int + len as int) % len as int) as int) >= 0,
        (((i as int - n as int + len as int) % len as int) as int) < len as int,
        (((i as int - n as int + len as int) % len as int) as usize) < len,
{
    lemma_mod_properties(i as int - n as int + len as int, len as int);
    let adjusted_index = (i as int - n as int + len as int) % len as int;
    assert(0 <= adjusted_index < len as int);
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
    if l.len() == 0 {
        return Seq::empty();
    }
    
    let len = l.len();
    let mut result = Seq::empty();
    let mut i: usize = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==>
                result@[j] == l@[(((j as int - n + len as int) % len as int) as usize)],
    {
        proof {
            lemma_mod_usize_conversion(i, n as usize, len);
        }
        let adjusted_index = (((i as int - n + len as int) % len as int) as usize);
        result = result.push(l[adjusted_index]);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}