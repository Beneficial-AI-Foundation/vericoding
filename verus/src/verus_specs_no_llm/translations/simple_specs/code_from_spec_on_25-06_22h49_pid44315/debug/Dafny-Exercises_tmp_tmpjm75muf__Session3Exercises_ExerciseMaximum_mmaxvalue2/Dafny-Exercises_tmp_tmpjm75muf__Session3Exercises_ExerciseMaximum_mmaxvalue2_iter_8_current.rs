use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mmaximum2(v: Vec<int>) -> (i: usize) 
    requires v.len() > 0
    ensures 0 <= i < v.len() 
    ensures forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k]
{
    let mut i: usize = 0;
    let mut j: usize = 1;
    
    while j < v.len()
        invariant 
            0 <= i < v.len(),
            1 <= j <= v.len(),
            i < j,
            forall|k: int| 0 <= k < j ==> v[i as int] >= v[k]
    {
        if v[j as int] > v[i as int] {
            i = j;
        }
        j = j + 1;
    }
    
    // After the loop, prove the postcondition
    proof {
        assert(j == v.len());
        assert(forall|k: int| 0 <= k < j ==> v[i as int] >= v[k]);
        assert(forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k]) by {
            assert(j == v.len());
        };
    }
    
    i
}

fn mmaxvalue2(v: Vec<int>) -> (m: int)
    requires v.len() > 0
    ensures forall|k: int| 0 <= k < v.len() ==> m >= v[k]
    ensures exists|i: int| 0 <= i < v.len() && m == v[i]
{
    let mut m = v[0];
    let mut j: usize = 1;
    
    while j < v.len()
        invariant
            1 <= j <= v.len(),
            forall|k: int| 0 <= k < j ==> m >= v[k],
            exists|i: int| 0 <= i < j && m == v[i]
    {
        if v[j as int] > m {
            m = v[j as int];
            proof {
                assert(exists|i: int| 0 <= i < j + 1 && m == v[i]) by {
                    assert(0 <= j < j + 1 && m == v[j as int]);
                };
            }
        } else {
            proof {
                assert(exists|i: int| 0 <= i < j + 1 && m == v[i]) by {
                    let old_i = choose|i: int| 0 <= i < j && m == v[i];
                    assert(0 <= old_i < j + 1 && m == v[old_i]);
                };
            }
        }
        j = j + 1;
    }
    
    // After the loop, prove the postconditions
    proof {
        assert(j == v.len());
        assert(forall|k: int| 0 <= k < v.len() ==> m >= v[k]) by {
            assert(forall|k: int| 0 <= k < j ==> m >= v[k]);
            assert(j == v.len());
        };
        assert(exists|i: int| 0 <= i < v.len() && m == v[i]) by {
            let witness_i = choose|i: int| 0 <= i < j && m == v[i];
            assert(0 <= witness_i < v.len() && m == v[witness_i]) by {
                assert(j == v.len());
            };
        };
    }
    
    m
}

}