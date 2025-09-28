use vstd::prelude::*;

verus! {

spec fn in_array(a: &[i32], x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
fn is_in_slice(s: &[i32], x: i32) -> (result: bool)
    ensures
        result == in_array(s, x)
{
    let mut i = 0;
    while i < s.len() 
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> s@[j] != x
        decreases s.len() - i
    {
        if s[i] == x {
            proof {
                s@[i as int] == x;
            }
            return true;
        }
        i += 1;
    }
    false
}

fn contains_in_vec(v: &Vec<i32>, x: i32) -> (result: bool)
    ensures
        result == exists|i: int| 0 <= i < v.len() && v@[i] == x
{
    let mut i = 0;
    while i < v.len() 
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v@[j] != x
        decreases v.len() - i
    {
        if v[i] == x {
            proof {
                v@[i as int] == x;
            }
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn shared_elements(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    ensures
        // All elements in the output are in both a and b
        forall|x: i32| result@.contains(x) ==> (in_array(a, x) && in_array(b, x)),
        // The elements in the output are all different
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: i32| result@.contains(x) ==> 
                (in_array(a, x) && in_array(b, x)),
            forall|j: int, k: int| 0 <= j < k < result.len() ==> 
                result@[j] != result@[k]
        decreases a.len() - i
    {
        let x = a[i];
        if is_in_slice(b, x) && !contains_in_vec(&result, x) {
            proof {
                // x is in a since it's a[i]
                // x is in b by is_in_slice true
                // x not in result by contains check
            }
            result.push(x);
        }
        i += 1;
        proof {
            assert(forall|x: i32| result@.contains(x) ==> 
                (in_array(a, x) && in_array(b, x)));
            assert(forall|j: int, k: int| 0 <= j < k < result.len() ==> 
                result@[j] != result@[k]);
        }
    }
    result
}
// </vc-code>

fn main() {
}

}