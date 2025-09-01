use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn find_smallest_even_index(s: Seq<u32>, start: usize) -> (index: int)
    recommends
        start <= s.len(),
    ensures
        index == -1 || (start as int <= index && index < s.len() as int && s[index] % 2 == 0),
        index == -1 ==> forall|i: int| start as int <= i < s.len() as int ==> s[i] % 2 != 0,
        index >= 0 ==> forall|i: int| start as int <= i < s.len() as int ==> 
            s[i] % 2 != 0 || s[index as int] <= s[i]
{
    if start >= s.len() {
        -1
    } else {
        let current_idx = start as int;
        if s[current_idx] % 2 == 0 {
            current_idx
        } else {
            find_smallest_even_index(s, start + 1)
        }
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
                s[i] % 2 != 0 || s[idx as int] <= s[i]
        }) && (find_smallest_even_index(s, start) == -1 ==> 
            forall|i: int| start as int <= i < s.len() as int ==> s[i] % 2 != 0)
{
    if start < s.len() {
        let current_idx = start as int;
        if s[current_idx] % 2 == 0 {
            assert forall|i: int| start as int <= i < s.len() as int implies 
                s[i] % 2 != 0 || s[current_idx] <= s[i] by {
                if i == current_idx {
                    assert(s[current_idx] <= s[i]);
                } else {
                    find_smallest_even_index_ensures(s, start + 1);
                    let next_idx = find_smallest_even_index(s, start + 1);
                    if next_idx >= 0 {
                        assert(s[next_idx as int] % 2 == 0);
                        assert(s[next_idx as int] <= s[i]);
                        assert(s[current_idx] <= s[next_idx as int]) by {
                            assert(s[current_idx] % 2 != 0);
                        };
                        assert(s[current_idx] <= s[i]);
                    } else {
                        assert(s[i] % 2 != 0);
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
    
    proof {
        find_smallest_even_index_ensures(nodes@, 0);
    }
    
    let spec_index = find_smallest_even_index(nodes@, 0);
    
    if spec_index >= 0 as int {
        proof {
            assert(0 <= spec_index && spec_index < nodes@.len() as int);
            assert(nodes@[spec_index as usize] % 2 == 0);
            assert(forall|i: int| 0 <= i < nodes@.len() as int && nodes@[i as usize] % 2 == 0 ==> 
                nodes@[spec_index as usize] <= nodes@[i as usize]);
        }
        let value = nodes@[spec_index as usize];
        let index_u32 = spec_index as u32;
        result.push(value);
        result.push(index_u32);
    }
    
    result
}
// </vc-code>

fn main() {}
}