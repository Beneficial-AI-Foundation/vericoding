use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn sorted_sublist(s: Seq<i32>, start: int, end: int) -> bool {
    forall|i: int, j: int| 
        start <= i && i < j && j < end ==> s[i] <= s[j]
}

proof fn sorted_sublist_transitive(s: Seq<i32>, a: int, b: int, c: int)
    requires
        sorted_sublist(s, a, b),
        sorted_sublist(s, b, c),
        a <= b && b <= c,
    ensures
        sorted_sublist(s, a, c),
{
    assert forall|i: int, j: int| a <= i && i < j && j < c implies s[i] <= s[j] by {
        if j < b {
            assert(s[i] <= s[j]) by {
                assert(sorted_sublist(s, a, b));
            }
        } else {
            assert(i < b) by {
                if i >= b {
                    assert(i >= b && j > i && j < c);
                    assert(false);
                }
            };
            assert(s[i] <= s[b]) by {
                assert(sorted_sublist(s, a, b));
            };
            assert(s[b] <= s[j]) by {
                assert(sorted_sublist(s, b, c));
            };
            assert(s[i] <= s[j]);
        }
    };
}

spec fn unique_seq(s: Seq<i32>, start: int, end: int) -> bool {
    forall|i: int, j: int| 
        start <= i && i < j && j < end ==> s[i] != s[j]
}

proof fn unique_seq_subrange(s: Seq<i32>, a: int, b: int, c: int)
    requires
        unique_seq(s, a, c),
        a <= b && b <= c,
    ensures
        unique_seq(s, a, b) && unique_seq(s, b, c),
{
}

spec fn contains_leq(s: Seq<i32>, val: i32, start: int, end: int) -> bool {
    exists|i: int| start <= i && i < end && s[i] <= val
}

spec fn contains_geq(s: Seq<i32>, val: i32, start: int, end: int) -> bool {
    exists|i: int| start <= i && i < end && s[i] >= val
}

proof fn contains_leq_insert(s: Seq<i32>, idx: int, val: i32, start: int, end: int)
    requires
        start <= idx && idx < end,
        #![trigger contains_leq(s.insert(idx, val), val, start, end + 1)]
    ensures
        contains_leq(s.insert(idx, val), val, start, end + 1),
{
}

proof fn contains_leq_preserved(s1: Seq<i32>, s2: Seq<i32>, val: i32, start: int, end: int)
    requires
        forall|i: int| start <= i && i < end ==> s1[i] == s2[i],
        #![trigger contains_leq(s1, val, start, end)]
        #![trigger contains_leq(s2, val, start, end)]
    ensures
        contains_leq(s1, val, start, end) == contains_leq(s2, val, start, end),
{
}

proof fn sorted_sublist_insert(s: Seq<i32>, idx: int, val: i32, start: int, end: int)
    requires
        start <= idx && idx <= end,
        forall|k: int| start <= k && k < idx ==> s[k] < val,
        forall|k: int| idx <= k && k < end ==> val <= s[k],
        sorted_sublist(s, start, end),
        #![trigger sorted_sublist(s.insert(idx, val), start, end + 1)]
    ensures
        sorted_sublist(s.insert(idx, val), start, end + 1),
{
    assert forall|i: int, j: int| start <= i && i < j && j < end + 1 implies s.insert(idx, val)[i] <= s.insert(idx, val)[j] by {
        if j == idx {
            if i == idx {
                assert(false);
            }
            assert(i < idx);
            assert(s.insert(idx, val)[i] == s[i]);
            assert(s.insert(idx, val)[j] == val);
            assert(s[i] < val);
        } else if i == idx {
            assert(j > idx);
            assert(s.insert(idx, val)[i] == val);
            assert(s.insert(idx, val)[j] == s[j - 1]);
            assert(val <= s[j - 1]);
        } else if i < idx && j < idx {
            assert(s.insert(idx, val)[i] == s[i]);
            assert(s.insert(idx, val)[j] == s[j]);
            assert(s[i] <= s[j]);
        } else if i >= idx && j >= idx {
            assert(s.insert(idx, val)[i] == s[i - 1]);
            assert(s.insert(idx, val)[j] == s[j - 1]);
            assert(s[i - 1] <= s[j - 1]);
        } else {
            assert(i < idx && j > idx);
            assert(s.insert(idx, val)[i] == s[i]);
            assert(s.insert(idx, val)[j] == s[j - 1]);
            assert(s[i] <= val);
            assert(val <= s[j - 1]);
            assert(s[i] <= s[j - 1]);
        }
    };
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len() 
        invariant 
            0 <= i && i <= a.len(),
            sorted_sublist(result@, 0, result.len() as int),
            unique_seq(result@, 0, result.len() as int),
            forall|j: int| 
                0 <= j && j < result.len() as int ==> 
                contains_leq(a@, result@[j], i as int, a.len() as int),
            forall|val: i32| 
                contains_leq(a@, val, i as int, a.len() as int) ==>
                contains_leq(result@, val, 0, result.len() as int),
        decreases a.len() - i
    {
        let current = a[i];
        let mut should_add = true;
        let mut j: usize = 0;
        
        while j < result.len() 
            invariant 
                0 <= j && j <= result.len(),
                should_add == (forall|k: int| 0 <= k && k < j as int ==> result@[k] != current),
            decreases result.len() - j
        {
            if result[j] == current {
                should_add = false;
                break;
            }
            j += 1;
        }
        
        if should_add {
            let mut k: usize = 0;
            
            while k < result.len() && result[k] < current 
                invariant 
                    0 <= k && k <= result.len(),
                    forall|l: int| 0 <= l && l < k as int ==> result@[l] < current,
                decreases result.len() - k
            {
                k += 1;
            }
            
            proof {
                let old_result = result@;
                result.insert(k, current);
                assert(forall|val: i32| 
                    contains_leq(a@, val, i as int + 1, a.len() as int) ==>
                    contains_leq(result@, val, 0, result.len() as int)) by {
                    assert forall|val: i32| contains_leq(a@, val, i as int + 1, a.len() as int) implies 
                        contains_leq(result@, val, 0, result.len() as int) by {
                        if contains_leq(a@, val, i as int, a.len() as int) {
                            assert(contains_leq(old_result, val, 0, old_result.len()));
                            if val == current {
                                assert(contains_leq(result@, val, 0, result.len() as int));
                            } else {
                                assert(contains_leq(result@, val, 0, result.len() as int));
                            }
                        } else {
                            assert(val >= current);
                            assert(contains_leq(result@, val, 0, result.len() as int));
                        }
                    }
                };
                sorted_sublist_insert(old_result, k as int, current, 0, old_result.len() as int);
            }
        } else {
            proof {
                assert(contains_leq(a@, current, i as int, a.len() as int));
                assert(contains_leq(result@, current, 0, result.len() as int));
                assert forall|val: i32| 
                    contains_leq(a@, val, i as int + 1, a.len() as int) implies 
                    contains_leq(result@, val, 0, result.len() as int) by {
                    if val == current {
                        assert(contains_leq(result@, val, 0, result.len() as int));
                    } else {
                        assert(contains_leq(a@, val, i as int, a.len() as int));
                        assert(contains_leq(result@, val, 0, result.len() as int));
                    }
                };
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}