// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by using correct lemma */
fn contains_element(v: &Vec<i32>, x: i32) -> (b: bool)
    ensures b == v.view().contains(x)
{
    let mut i = 0;
    while i < v.len()
        invariant
            !v.view().take(i as int).contains(x),
        decreases v.len() - i,
    {
        if v[i] == x {
            assert(v.view().contains(x));
            return true;
        }
        
        i = i + 1;
    }
    proof {
        assert(v.view().take(v.len() as int) == v.view()) by {
            vstd::seq_lib::lemma_take_full(v.view());
        };
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn set_to_seq(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],

        forall|i: int| 0 <= i < result.len() ==> 
            exists|j: int| 0 <= j < s.len() && s[j] == #[trigger] result[i],

        forall|i: int| 0 <= i < s.len() ==> 
            exists|j: int| 0 <= j < result.len() && result[j] == #[trigger] s[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed api calls and macro usage */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
            result.view().to_set() == s.view().take(i as int).to_set(),
        decreases s.len() - i,
    {
        let x = s[i];
        let contains = contains_element(&result, x);

        proof {
            assert(s.view().take((i + 1) as int) == s.view().take(i as int).push(x)) by {
                vstd::seq_lib::lemma_take_plus_one(i as int, s.view());
            };
            assert(s.view().take((i + 1) as int).to_set() == s.view().take(i as int).to_set().insert(x)) by(set_equal);
        }
        
        if !contains {
            let ghost old_view = result.view();
            result.push(x);
            proof {
                vstd::seq_lib::lemma_push_no_duplicates(old_view, x);
                assert(result.view().to_set() == old_view.to_set().insert(x)) by(set_equal);
            }
        } else {
            proof {
                let result_set = result.view().to_set();
                let s_take_i_set = s.view().take(i as int).to_set();
                assert(result_set.contains(x));
                assert(s_take_i_set.contains(x));
                vstd::set_lib::lemma_insert_same(s_take_i_set, x);
                assert(s_take_i_set.insert(x) == s_take_i_set);
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(s.view().take(s.len() as int) == s.view()) by {
            vstd::seq_lib::lemma_take_full(s.view());
        };
        assert(result.view().to_set() == s.view().to_set()) by(set_equal);
    }
    
    result
}
// </vc-code>

}
fn main() {}