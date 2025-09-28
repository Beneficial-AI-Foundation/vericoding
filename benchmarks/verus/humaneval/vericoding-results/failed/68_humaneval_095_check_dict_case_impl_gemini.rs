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
/* helper modified by LLM (iteration 5): No changes needed, helpers are correct. */
fn is_lower_case_exec(s: &Vec<char>) -> (res: bool)
    ensures
        res == is_lower_case(s@),
{
    let mut i = 0;
    while i < s.len()
        invariant
            forall|j: int| 0 <= j < i ==> ('a' <= s@[j] <= 'z'),
        decreases s.len() - i
    {
        if !('a' <= s[i] && s[i] <= 'z') {
            return false;
        }
        i = i + 1;
    }
    true
}

fn is_upper_case_exec(s: &Vec<char>) -> (res: bool)
    ensures
        res == is_upper_case(s@),
{
    let mut i = 0;
    while i < s.len()
        invariant
            forall|j: int| 0 <= j < i ==> ('A' <= s@[j] <= 'Z'),
        decreases s.len() - i
    {
        if !('A' <= s[i] && s[i] <= 'Z') {
            return false;
        }
        i = i + 1;
    }
    true
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
    /* code modified by LLM (iteration 5): Fixed compilation errors and proof block details. */
    if dict.len() == 0 as nat {
        return false;
    }

    let keys = dict.get_keys();
    let mut i: usize = 0;
    let mut all_lower = true;
    let mut all_upper = true;

    while i < keys.len()
        invariant
            dict.len() > 0,
            keys@.to_set() == dict.dom(),
            keys@.no_duplicates(),
            0 <= i <= keys.len(),
            all_lower == (forall|j: int| 0 <= j < i ==> is_lower_case(keys@[j]@)),
            all_upper == (forall|j: int| 0 <= j < i ==> is_upper_case(keys@[j]@)),
        decreases keys.len() - i
    {
        let k = &keys[i];
        if !is_lower_case_exec(k) {
            all_lower = false;
        }
        if !is_upper_case_exec(k) {
            all_upper = false;
        }
        i = i + 1;
    }

    let result = all_lower || all_upper;

    proof {
        if result {
            if all_lower {
                assert(forall|j: int| 0 <= j < keys.len() ==> is_lower_case(keys@[j]@));
                assert forall|k: Vec<char>| #[trigger] dict.contains_key(k) implies is_lower_case(k@) by {
                    assert(dict.dom().contains(k@));
                    assert(keys@.to_set().contains(k@));
                    let j = choose|j: int| 0 <= j < keys.len() && keys@[j] == k@;
                    assert(is_lower_case(keys@[j]@));
                };
            } else {
                assert(all_upper);
                assert(forall|j: int| 0 <= j < keys.len() ==> is_upper_case(keys@[j]@));
                assert forall|k: Vec<char>| #[trigger] dict.contains_key(k) implies is_upper_case(k@) by {
                    assert(dict.dom().contains(k@));
                    assert(keys@.to_set().contains(k@));
                    let j = choose|j: int| 0 <= j < keys.len() && keys@[j] == k@;
                    assert(is_upper_case(keys@[j]@));
                };
            }
        } else {
            assert(dict.len() > 0);

            assert(!all_lower);
            let j_lower = choose|j: int| 0 <= j < keys.len() && !is_lower_case(keys@[j]@);
            let k_lower = keys[j_lower as usize].clone();
            assert(dict.contains_key(k_lower));
            assert(exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_lower_case(k@));

            assert(!all_upper);
            let j_upper = choose|j: int| 0 <= j < keys.len() && !is_upper_case(keys@[j]@);
            let k_upper = keys[j_upper as usize].clone();
            assert(dict.contains_key(k_upper));
            assert(exists|k: Vec<char>| #[trigger] dict.contains_key(k) && !is_upper_case(k@));
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}