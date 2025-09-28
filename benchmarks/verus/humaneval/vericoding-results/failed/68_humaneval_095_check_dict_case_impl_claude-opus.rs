// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lower_case(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> ('a' <= #[trigger] s[i] <= 'z')
}

spec fn is_upper_case(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> ('A' <= #[trigger] s[i] <= 'Z')
}

type DictCase = Map<Seq<char>, Seq<char>>;
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn check_dict_case(dict: Map<Vec<char>, Vec<char>>) -> (result: bool)
    ensures
        (dict.len() == 0) ==> !result,
        result ==> ((forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@)) || (forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@))),
        !result ==> ((dict.len() == 0) || ((exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_lower_case(k@)) && (exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_upper_case(k@))))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed int/nat type error - use usize for indexing */
    if dict.len() == 0 {
        return false;
    }
    
    let mut all_lower = true;
    let mut all_upper = true;
    
    let dom = dict.dom();
    let mut idx: usize = 0;
    
    while idx < dom.len()
        invariant
            0 <= idx <= dom.len(),
            all_lower ==> forall|j: int| 0 <= j < idx ==> is_lower_case(dom[j]@),
            all_upper ==> forall|j: int| 0 <= j < idx ==> is_upper_case(dom[j]@),
            !all_lower ==> exists|j: int| 0 <= j < idx && !is_lower_case(dom[j]@),
            !all_upper ==> exists|j: int| 0 <= j < idx && !is_upper_case(dom[j]@)
    {
        let key = dom[idx];
        let k = key@;
        let mut i: usize = 0;
        let mut key_is_lower = true;
        let mut key_is_upper = true;
        
        while i < k.len()
            invariant
                0 <= i <= k.len(),
                key_is_lower ==> forall|j: int| 0 <= j < i ==> 'a' <= k[j] <= 'z',
                key_is_upper ==> forall|j: int| 0 <= j < i ==> 'A' <= k[j] <= 'Z'
        {
            let c = k[i as usize];
            if !(c >= 'a' && c <= 'z') {
                key_is_lower = false;
            }
            if !(c >= 'A' && c <= 'Z') {
                key_is_upper = false;
            }
            i = i + 1;
        }
        
        if !key_is_lower {
            all_lower = false;
        }
        if !key_is_upper {
            all_upper = false;
        }
        
        if !all_lower && !all_upper {
            return false;
        }
        
        idx = idx + 1;
    }
    
    all_lower || all_upper
}
// </vc-code>


}

fn main() {}