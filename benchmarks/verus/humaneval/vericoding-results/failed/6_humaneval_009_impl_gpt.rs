// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_up_to(numbers: Seq<int>, index: int) -> int
    decreases index when 0 <= index < numbers.len()
{
    if 0 <= index < numbers.len() {
        if index == 0 {
            numbers[0]
        } else {
            let prev_max = max_up_to(numbers, index - 1);
            if numbers[index] > prev_max { numbers[index] } else { prev_max }
        }
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn vec_to_seq_int(v: Vec<i8>) -> Seq<int> {
    v@.map(|i, x| x as int)
}

/* helper modified by LLM (iteration 5): lemma that max_up_to is an upper bound on all previous elements */
proof fn lemma_max_up_to_upper_bound(numbers: Seq<int>, i: int)
    requires
        0 <= i < numbers.len(),
    ensures
        forall|j: int| 0 <= j <= i ==> numbers[j] <= max_up_to(numbers, i),
    decreases i
{
    if i == 0 {
        assert forall|j: int| 0 <= j <= i ==> numbers[j] <= max_up_to(numbers, i) by {
            if 0 <= j <= i {
                assert(j == 0);
                assert(max_up_to(numbers, i) == numbers[0]);
                assert(numbers[0] <= numbers[0]);
            }
        };
    } else {
        lemma_max_up_to_upper_bound(numbers, i - 1);
        assert forall|j: int| 0 <= j <= i ==> numbers[j] <= max_up_to(numbers, i) by {
            let prev = max_up_to(numbers, i - 1);
            assert(max_up_to(numbers, i) == if numbers[i] > prev { numbers[i] } else { prev });
            if 0 <= j <= i {
                if j < i {
                    assert(0 <= j <= i - 1);
                    assert(numbers[j] <= prev);
                    assert(prev <= if numbers[i] > prev { numbers[i] } else { prev }) by {
                        if numbers[i] > prev {
                            assert(prev <= numbers[i]);
                        } else {
                            assert(prev <= prev);
                        }
                    };
                    assert(numbers[j] <= if numbers[i] > prev { numbers[i] } else { prev });
                } else {
                    assert(j == i);
                    if numbers[i] > prev {
                        assert(numbers[i] <= numbers[i]);
                        assert(numbers[i] <= if numbers[i] > prev { numbers[i] } else { prev });
                    } else {
                        assert(numbers[i] <= prev);
                        assert(numbers[i] <= if numbers[i] > prev { numbers[i] } else { prev });
                    }
                }
            }
        };
    }
}

/* helper modified by LLM (iteration 5): lemma that some index attains max_up_to */
proof fn lemma_max_up_to_exists(numbers: Seq<int>, i: int)
    requires
        0 <= i < numbers.len(),
    ensures
        exists|j: int| 0 <= j <= i && numbers[j] == max_up_to(numbers, i),
    decreases i
{
    if i == 0 {
        assert(exists|j: int| 0 <= j <= i && numbers[j] == max_up_to(numbers, i)) by {
            assert(max_up_to(numbers, i) == numbers[0]);
            assert(0 <= 0 <= i);
            assert(numbers[0] == max_up_to(numbers, i));
        };
    } else {
        lemma_max_up_to_exists(numbers, i - 1);
        let prev = max_up_to(numbers, i - 1);
        assert(exists|j: int| 0 <= j <= i && numbers[j] == max_up_to(numbers, i)) by {
            assert(max_up_to(numbers, i) == if numbers[i] > prev { numbers[i] } else { prev });
            if numbers[i] > prev {
                assert(0 <= i <= i);
                assert(numbers[i] == max_up_to(numbers, i));
            } else {
                let j_prev = choose|j: int| 0 <= j <= i - 1 && numbers[j] == prev;
                assert(0 <= j_prev <= i - 1);
                assert(0 <= j_prev <= i);
                assert(max_up_to(numbers, i) == prev);
                assert(numbers[j_prev] == max_up_to(numbers, i));
            }
        };
    }
}
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == numbers.len() &&
        (numbers.len() == 0 ==> result.len() == 0) &&
        (numbers.len() > 0 ==> result.len() > 0) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            result[i] as int == max_up_to(vec_to_seq_int(numbers), i)) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            forall|j: int| #![trigger numbers@[j]] 0 <= j <= i ==> numbers@[j] as int <= result[i] as int) &&
        (forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==>
            exists|j: int| 0 <= j <= i && numbers@[j] as int == result[i] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement rolling max iteratively with proofs connecting to spec */
    let mut res: Vec<i8> = Vec::new();
    let seq = vec_to_seq_int(numbers);
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i as int <= numbers.len() as int,
            res.len() == i,
            forall|k: int| 0 <= k < i as int ==> res@[k] as int == max_up_to(seq, k),
        decreases (numbers.len() - i) as int
    {
        let cur: i8 = numbers[i];
        if i == 0 {
            res.push(cur);
            proof {
                assert(res@[0] == cur);
                assert(seq[0] == numbers@[0] as int);
                assert(numbers@[0] == cur);
                assert(res@[0] as int == seq[0]);
                assert(max_up_to(seq, 0) == seq[0]);
            }
        } else {
            let prev_max: i8 = res[i - 1];
            let new_val: i8 = if cur > prev_max { cur } else { prev_max };
            res.push(new_val);
            proof {
                let ii = i as int;
                let prev_int = res@[(ii - 1)] as int;
                assert(prev_int == max_up_to(seq, ii - 1));
                assert(res@[ii] == new_val);
                assert(numbers@[ii] == cur);
                assert(seq[ii] == numbers@[ii] as int);
                assert(cur as int == seq[ii]);
                assert(res@[(ii - 1)] == prev_max);
                assert(prev_max as int == prev_int);
                assert(res@[ii] as int == if cur > prev_max { cur as int } else { prev_max as int });
                assert(res@[ii] as int == if seq[ii] > prev_int { seq[ii] } else { prev_int });
                assert(max_up_to(seq, ii) == if seq[ii] > prev_int { seq[ii] } else { prev_int });
                assert(res@[ii] as int == max_up_to(seq, ii));
            }
        }
        proof {
            let ii = i as int;
            assert forall|k: int| 0 <= k < ii + 1 ==> res@[k] as int == max_up_to(seq, k) by {
                if 0 <= k < ii {
                    // from invariant
                } else {
                    assert(k == ii);
                    if i == 0 {
                        assert(res@[0] as int == seq[0]);
                        assert(max_up_to(seq, 0) == seq[0]);
                    } else {
                        let prev_int = res@[(ii - 1)] as int;
                        assert(prev_int == max_up_to(seq, ii - 1));
                        assert(res@[ii] as int == if seq[ii] > prev_int { seq[ii] } else { prev_int });
                        assert(max_up_to(seq, ii) == if seq[ii] > prev_int { seq[ii] } else { prev_int });
                    }
                }
            };
        }
        i = i + 1;
    }

    proof {
        assert forall|ii: int| 0 <= ii < res.len() as int ==>
            forall|j: int| 0 <= j <= ii ==> numbers@[j] as int <= res@[ii] as int
        by {
            if 0 <= ii < res.len() as int {
                lemma_max_up_to_upper_bound(seq, ii);
                assert(res@[ii] as int == max_up_to(seq, ii));
                assert forall|j: int| 0 <= j <= ii ==> numbers@[j] as int <= res@[ii] as int by {
                    if 0 <= j <= ii {
                        assert(numbers@[j] as int <= max_up_to(seq, ii));
                        assert(res@[ii] as int == max_up_to(seq, ii));
                    }
                };
            }
        };

        assert forall|ii: int| 0 <= ii < res.len() as int ==>
            exists|j: int| 0 <= j <= ii && numbers@[j] as int == res@[ii] as int
        by {
            if 0 <= ii < res.len() as int {
                lemma_max_up_to_exists(seq, ii);
                let j0 = choose|j: int| 0 <= j <= ii && seq[j] == max_up_to(seq, ii);
                assert(0 <= j0 <= ii);
                assert(res@[ii] as int == max_up_to(seq, ii));
                assert(seq[j0] == numbers@[j0] as int);
                assert(numbers@[j0] as int == res@[ii] as int);
            }
        };
    }

    res
}
// </vc-code>


}

fn main() {}