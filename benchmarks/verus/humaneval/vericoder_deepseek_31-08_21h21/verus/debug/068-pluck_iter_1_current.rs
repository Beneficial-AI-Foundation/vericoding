use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn find_smallest_even_index(s: Seq<u32>, start: usize) -> (index: int)
    recommends
        start <= s.len(),
    ensures
        index == -1 || (0 <= index < s.len() as int && s[index] % 2 == 0),
        index == -1 ==> forall|i: int| start as int <= i < s.len() as int ==> s[i] % 2 != 0,
        index >= 0 ==> forall|i: int| start as int <= i < s.len() as int ==> 
            s[i] % 2 != 0 || s[index] <= s[i]
{
    if start >= s.len() {
        -1
    } else if s[start] % 2 == 0 {
        start as int
    } else {
        find_smallest_even_index(s, start + 1)
    }
}

proof fn find_smallest_even_index_ensures(s: Seq<u32>, start: usize)
    by(nonlinear_arith)
    requires
        start <= s.len(),
    ensures
        (find_smallest_even_index(s, start) >= 0 ==> {
            let idx = find_smallest_even_index(s, start);
            forall|i: int| start as int <= i < s.len() as int ==> 
                s[i] % 2 != 0 || s[idx] <= s[i]
        }) && (find_smallest_even_index(s, start) == -1 ==> 
            forall|i: int| start as int <= i < s.len() as int ==> s[i] % 2 != 0)
{
    if start < s.len() {
        if s[start] % 2 == 0 {
            assert forall|i: int| start as int <= i < s.len() as int implies 
                s[i] % 2 != 0 || s[start] <= s[i] by {
                if i == start as int {
                    assert(s[start] <= s[i]);
                } else {
                    find_smallest_even_index_ensures(s, start + 1);
                    let idx = find_smallest_even_index(s, start + 1);
                    if idx >= 0 {
                        assert(s[idx] % 2 == 0);
                        assert(s[idx] <= s[i]);
                        assert(s[start] > s[idx]) by { /* contradiction if smaller exists */ };
                    }
                }
            };
        } else {
            find_smallest_even_index_ensures(s, start + 1);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn pluck_smallest_even(nodes: &Vec<u32>) -> (result: Vec<u32>)
    // pre-conditions-start
    requires
        nodes@.len() <= u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result@.len() == 0 || result@.len() == 2,
        result@.len() == 0 ==> forall|i: int| 0 <= i < nodes@.len() ==> nodes@[i] % 2 != 0,
        result@.len() == 2 ==> {
            let node = result@[0];
            let index = result@[1];
            &&& 0 <= index < nodes@.len()
            &&& nodes@[index as int] == node
            &&& node % 2 == 0
            &&& forall|i: int|
                0 <= i < nodes@.len() && nodes@[i] % 2 == 0 ==> node <= nodes@[i] && forall|i: int|
                    0 <= i < result@[1] ==> nodes@[i] % 2 != 0 || nodes@[i] > node
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<u32> = Vec::new();
    let mut smallest_index: Option<usize> = None;
    let mut smallest_value: Option<u32> = None;
    
    proof {
        find_smallest_even_index_ensures(nodes@, 0);
    }
    
    let spec_index = find_smallest_even_index(nodes@, 0);
    
    if spec_index >= 0 {
        let idx = spec_index as usize;
        result.push(nodes[idx]);
        result.push(idx as u32);
        
        proof {
            assert(0 <= idx < nodes@.len());
            assert(nodes@[idx] % 2 == 0);
            assert(forall|i: int| 0 <= i < nodes@.len() && nodes@[i] % 2 == 0 ==> 
                nodes@[idx] <= nodes@[i]);
            assert(forall|i: int| 0 <= i < idx ==> nodes@[i] % 2 != 0 || nodes@[i] > nodes@[idx]);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}