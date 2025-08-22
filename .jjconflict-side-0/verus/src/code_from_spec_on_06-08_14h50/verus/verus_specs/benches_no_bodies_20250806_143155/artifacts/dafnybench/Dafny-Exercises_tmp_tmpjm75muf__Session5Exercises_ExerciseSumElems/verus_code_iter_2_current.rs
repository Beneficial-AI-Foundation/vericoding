use vstd::prelude::*;

verus! {
    // Right-to-left sum function (equivalent to Dafny's SumR)
    spec fn sum_r(s: Seq<int>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
        }
    }

    // Left-to-right sum function (equivalent to Dafny's SumL)
    spec fn sum_l(s: Seq<int>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            s[0] + sum_l(s.subrange(1, s.len() as int))
        }
    }

    // Lemma about concatenation and taking all but last element
    proof fn concat_last(s: Seq<int>, t: Seq<int>)
        requires t.len() > 0
        ensures (s + t).subrange(0, (s + t).len() - 1) == s + t.subrange(0, t.len() - 1)
    {
        assert((s + t).len() == s.len() + t.len());
        assert((s + t).len() - 1 == s.len() + t.len() - 1);
        
        let concat = s + t;
        let left = concat.subrange(0, concat.len() - 1);
        let right = s + t.subrange(0, t.len() - 1);
        
        assert(left.len() == right.len());
        
        assert forall |i: int| 0 <= i < left.len() implies left[i] == right[i] by {
            if i < s.len() {
                assert(left[i] == concat[i] == s[i] == right[i]);
            } else {
                assert(left[i] == concat[i] == t[i - s.len()]);
                assert(right[i] == t.subrange(0, t.len() - 1)[i - s.len()] == t[i - s.len()]);
            }
        };
    }

    // Lemma about concatenation and taking all but first element
    proof fn concat_first(s: Seq<int>, t: Seq<int>)
        requires s.len() > 0
        ensures (s + t).subrange(1, (s + t).len() as int) == s.subrange(1, s.len() as int) + t
    {
        let concat = s + t;
        let left = concat.subrange(1, concat.len() as int);
        let right = s.subrange(1, s.len() as int) + t;
        
        assert(left.len() == right.len());
        
        assert forall |i: int| 0 <= i < left.len() implies left[i] == right[i] by {
            if i < s.len() - 1 {
                assert(left[i] == concat[i + 1] == s[i + 1]);
                assert(right[i] == s.subrange(1, s.len() as int)[i] == s[i + 1]);
            } else {
                assert(left[i] == concat[i + 1] == t[i + 1 - s.len()] == t[i - (s.len() - 1)]);
                assert(right[i] == t[i - (s.len() - 1)]);
            }
        };
    }

    // Lemma: SumR distributes over concatenation
    proof fn sum_by_parts_r(s: Seq<int>, t: Seq<int>)
        ensures sum_r(s + t) == sum_r(s) + sum_r(t)
        decreases s.len(), t.len()
    {
        if t.len() == 0 {
            assert(s + t == s);
        } else if s.len() == 0 {
            assert(s + t == t);
        } else {
            concat_last(s, t);
            sum_by_parts_r(s, t.subrange(0, t.len() - 1));
        }
    }

    // Lemma: SumL distributes over concatenation
    proof fn sum_by_parts_l(s: Seq<int>, t: Seq<int>)
        ensures sum_l(s + t) == sum_l(s) + sum_l(t)
        decreases s.len(), t.len()
    {
        if t.len() == 0 {
            assert(s + t == s);
        } else if s.len() == 0 {
            assert(s + t == t);
        } else {
            concat_first(s, t);
            sum_by_parts_l(s.subrange(1, s.len() as int), t);
        }
    }

    // Lemma: SumR equals SumL for any subsequence
    proof fn equal_sum_r(s: Seq<int>, i: int, j: int)
        requires 0 <= i <= j <= s.len()
        ensures sum_r(s.subrange(i, j)) == sum_l(s.subrange(i, j))
        decreases j - i
    {
        if i == j {
            // Empty subsequence
        } else {
            equal_sum_r(s, i, j-1);
            let sub = s.subrange(i, j-1);
            let last = seq![s[(j-1) as int]];
            assert(s.subrange(i, j) == sub + last);
            sum_by_parts_l(sub, last);
        }
    }

    // Sum function for arrays (equivalent to Dafny's SumV)
    spec fn sum_v(v: &[int], c: int, f: int) -> int
        recommends 0 <= c <= f <= v.len()
    {
        sum_r(v@.subrange(c, f))
    }

    // Array facts lemma
    proof fn array_facts<T>() {
        // Basic facts about arrays and their sequence views
    }

    // Sum elements method - forward iteration (equivalent to Dafny's sumElems)
    fn sum_elems(v: &[i32]) -> (sum: i32)
        requires v.len() < 100  // Bound to prevent overflow
        ensures sum as int == sum_r(v@.map(|i, x| x as int))
    {
        let mut sum = 0i32;
        let mut i = 0;
        
        while i < v.len()
            invariant 
                0 <= i <= v.len(),
                sum as int == sum_r(v@.subrange(0, i as int).map(|j, x| x as int))
        {
            proof {
                let prev_seq = v@.subrange(0, i as int).map(|j, x| x as int);
                /* code modified by LLM (iteration 1): Fixed type casting in seq construction */
                let new_elem = seq![v[i as int] as int];
                let new_seq = v@.subrange(0, (i + 1) as int).map(|j, x| x as int);
                
                assert(new_seq == prev_seq + new_elem);
                sum_by_parts_r(prev_seq, new_elem);
            }
            
            sum = sum + v[i];
            i = i + 1;
        }
        
        assert(v@.subrange(0, i as int) == v@);
        sum
    }

    // Sum elements method - backward iteration (equivalent to Dafny's sumElemsB)
    fn sum_elems_b(v: &[i32]) -> (sum: i32)
        requires v.len() < 100  // Bound to prevent overflow
        ensures sum as int == sum_r(v@.map(|i, x| x as int))
    {
        let mut sum = 0i32;
        let mut i = v.len();
        
        while i > 0
            invariant 
                0 <= i <= v.len(),
                sum as int == sum_r(v@.subrange(i as int, v.len() as int).map(|j, x| x as int))
        {
            i = i - 1;
            
            proof {
                let prev_seq = v@.subrange((i + 1) as int, v.len() as int).map(|j, x| x as int);
                /* code modified by LLM (iteration 1): Fixed type casting in seq construction */
                let new_elem = seq![v[i as int] as int];
                let new_seq = v@.subrange(i as int, v.len() as int).map(|j, x| x as int);
                
                assert(new_seq == new_elem + prev_seq);
                sum_by_parts_r(new_elem, prev_seq);
            }
            
            sum = sum + v[i];
        }
        
        assert(v@.subrange(0, v.len() as int) == v@);
        sum
    }
}

fn main() {
    let v = [1, 2, 3, 4, 5];
    let sum1 = sum_elems(&v);
    let sum2 = sum_elems_b(&v);
    println!("Forward sum: {}, Backward sum: {}", sum1, sum2);
}