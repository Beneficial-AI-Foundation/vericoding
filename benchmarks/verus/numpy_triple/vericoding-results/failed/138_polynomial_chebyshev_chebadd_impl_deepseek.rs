// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed nat usage in exec code by using usize instead */
fn max_len(c1: &Vec<i8>, c2: &Vec<i8>) -> usize {
    if c1.len() >= c2.len() { c1.len() } else { c2.len() }
}

proof fn element_sum_preserved(c1: &Vec<i8>, c2: &Vec<i8>, result: &Vec<i8>, i: int)
    requires
        0 <= i < result.len() as int,
        result.len() == max_len(c1, c2),
    ensures
        if i < c1.len() as int && i < c2.len() as int {
            result[i] as int == c1[i] as int + c2[i] as int
        } else if i < c1.len() as int {
            result[i] == c1[i]
        } else if i < c2.len() as int {
            result[i] == c2[i]
        } else {
            result[i] == 0
        }
{
}

proof fn non_zero_preserved_c1(c1: &Vec<i8>, c2: &Vec<i8>, result: &Vec<i8>, i: int)
    requires
        0 <= i < c1.len() as int,
        c1[i] != 0,
        result.len() == max_len(c1, c2),
    ensures
        exists|j: int| 0 <= j < result.len() as int && j == i && {
            if i < c2.len() as int {
                result[j] as int == c1[i] as int + c2[i] as int
            } else {
                result[j] == c1[i]
            }
        }
{
}

proof fn non_zero_preserved_c2(c1: &Vec<i8>, c2: &Vec<i8>, result: &Vec<i8>, i: int)
    requires
        0 <= i < c2.len() as int,
        c2[i] != 0,
        result.len() == max_len(c1, c2),
    ensures
        exists|j: int| 0 <= j < result.len() as int && j == i && {
            if i < c1.len() as int {
                result[j] as int == c1[i] as int + c2[i] as int
            } else {
                result[j] == c2[i]
            }
        }
{
}
// </vc-helpers>

// <vc-spec>
fn chebadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int + c2[i] as int
            } else if i < c1.len() {
                result[i] == c1[i]
            } else if i < c2.len() {
                result[i] == c2[i]
            } else {
                result[i] == 0
            }
        },
        forall|i: int| 0 <= i < c1.len() ==> c1[i] != 0 ==> {
            exists|j: int| 0 <= j < result.len() && j == i && {
                if i < c2.len() {
                    result[j] as int == c1[i] as int + c2[i] as int
                } else {
                    result[j] == c1[i]
                }
            }
        },
        forall|i: int| 0 <= i < c2.len() ==> c2[i] != 0 ==> {
            exists|j: int| 0 <= j < result.len() && j == i && {
                if i < c1.len() {
                    result[j] as int == c1[i] as int + c2[i] as int
                } else {
                    result[j] == c2[i]
                }
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed max_len usage and removed nat casts */
    let max_len_uint = max_len(&c1, &c2);
    let mut result = Vec::<i8>::new();
    result.resize(max_len_uint, 0);
    
    let mut i: usize = 0;
    while i < max_len_uint
        invariant
            i <= max_len_uint,
            result.len() == max_len_uint,
            forall|j: int| 0 <= j < i as int ==> {
                if j < c1.len() as int && j < c2.len() as int {
                    result[j] as int == c1[j] as int + c2[j] as int
                } else if j < c1.len() as int {
                    result[j] == c1[j]
                } else if j < c2.len() as int {
                    result[j] == c2[j]
                } else {
                    result[j] == 0
                }
            }
    {
        if i < c1.len() && i < c2.len() {
            result[i] = (c1[i] as i16 + c2[i] as i16) as i8;
        } else if i < c1.len() {
            result[i] = c1[i];
        } else if i < c2.len() {
            result[i] = c2[i];
        }
        i = i + 1;
    }
    
    proof {
        let mut idx: int = 0;
        while idx < max_len_uint as int
            invariant
                0 <= idx <= max_len_uint as int,
                forall|j: int| 0 <= j < idx ==> {
                    if j < c1.len() as int && j < c2.len() as int {
                        result[j] as int == c1[j] as int + c2[j] as int
                    } else if j < c1.len() as int {
                        result[j] == c1[j]
                    } else if j < c2.len() as int {
                        result[j] == c2[j]
                    } else {
                        result[j] == 0
                    }
                }
        {
            element_sum_preserved(&c1, &c2, &result, idx);
            idx = idx + 1;
        }
        
        let mut idx_c1: int = 0;
        while idx_c1 < c1.len() as int
            invariant
                0 <= idx_c1 <= c1.len() as int,
                forall|j: int| 0 <= j < idx_c1 && c1[j] != 0 ==> {
                    exists|k: int| 0 <= k < result.len() as int && k == j && {
                        if j < c2.len() as int {
                            result[k] as int == c1[j] as int + c2[j] as int
                        } else {
                            result[k] == c1[j]
                        }
                    }
                }
        {
            if c1[idx_c1] != 0 {
                non_zero_preserved_c1(&c1, &c2, &result, idx_c1);
            }
            idx_c1 = idx_c1 + 1;
        }
        
        let mut idx_c2: int = 0;
        while idx_c2 < c2.len() as int
            invariant
                0 <= idx_c2 <= c2.len() as int,
                forall|j: int| 0 <= j < idx_c2 && c2[j] != 0 ==> {
                    exists|k: int| 0 <= k < result.len() as int && k == j && {
                        if j < c1.len() as int {
                            result[k] as int == c1[j] as int + c2[j] as int
                        } else {
                            result[k] == c2[j]
                        }
                    }
                }
        {
            if c2[idx_c2] != 0 {
                non_zero_preserved_c2(&c1, &c2, &result, idx_c2);
            }
            idx_c2 = idx_c2 + 1;
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}