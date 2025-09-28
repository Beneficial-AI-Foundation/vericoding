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
/* helper modified by LLM (iteration 5): fixed nat type error in helper functions */
spec fn all_keys_lower(dict: Map<Vec<char>, Vec<char>>) -> bool {
    forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_lower_case(k@)
}

spec fn all_keys_upper(dict: Map<Vec<char>, Vec<char>>) -> bool {
    forall|k: Vec<char>| #[trigger] dict.contains_key(k) ==> is_upper_case(k@)
}

spec fn exists_non_lower(dict: Map<Vec<char>, Vec<char>>) -> bool {
    exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_lower_case(k@)
}

spec fn exists_non_upper(dict: Map<Vec<char>, Vec<char>>) -> bool {
    exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_upper_case(k@)
}

fn check_key_case(key: &Vec<char>) -> (result: (bool, bool))
    ensures
        result.0 ==> is_lower_case(key@),
        result.1 ==> is_upper_case(key@),
{
    let mut is_lower = true;
    let mut is_upper = true;
    
    for i in 0..key.len()
        invariant
            is_lower ==> (forall|j: int| 0 <= j < i ==> ('a' <= key@[j] <= 'z')),
            is_upper ==> (forall|j: int| 0 <= j < i ==> ('A' <= key@[j] <= 'Z')),
    {
        let c = key[i];
        if !('a' <= c && c <= 'z') {
            is_lower = false;
        }
        if !('A' <= c && c <= 'Z') {
            is_upper = false;
        }
    }
    
    (is_lower, is_upper)
}

fn convert_keys_to_vec(dict: &Map<Vec<char>, Vec<char>>) -> (result: Vec<Vec<char>>)
    ensures
        forall|i: int| 0 <= i < result@.len() ==> dict.contains_key(result@[i]),
        forall|k: Vec<char>| dict.contains_key(k) ==> exists|i: int| 0 <= i < result@.len() && result@[i] == k,
{
    let mut keys = Vec::new();
    let mut remaining_keys = dict.dom();
    
    while !remaining_keys.is_empty()
        invariant
            forall|i: int| 0 <= i < keys@.len() ==> dict.contains_key(keys@[i]),
            forall|k: Vec<char>| dict.contains_key(k) ==> (remaining_keys.contains(k) || exists|i: int| 0 <= i < keys@.len() && keys@[i] == k),
            remaining_keys.subset_of(dict.dom()),
        decreases remaining_keys.len(),
    {
        let key = remaining_keys.choose();
        keys.push(key);
        remaining_keys = remaining_keys.remove(key);
    }
    
    keys
}
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
    /* code modified by LLM (iteration 5): removed nat suffix from number literal */
    if dict.len() == 0 {
        return false;
    }
    
    let mut all_lower = true;
    let mut all_upper = true;
    
    let keys = convert_keys_to_vec(&dict);
    
    for i in 0..keys.len()
        invariant
            all_lower ==> (forall|j: int| 0 <= j < i ==> is_lower_case(keys@[j]@)),
            all_upper ==> (forall|j: int| 0 <= j < i ==> is_upper_case(keys@[j]@)),
    {
        let key = &keys[i];
        let (key_is_lower, key_is_upper) = check_key_case(key);
        
        if !key_is_lower {
            all_lower = false;
        }
        if !key_is_upper {
            all_upper = false;
        }
    }
    
    all_lower || all_upper
}
// </vc-code>


}

fn main() {}