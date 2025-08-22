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
    }

    // Lemma about concatenation and taking all but first element
    proof fn concat_first(s: Seq<int>, t: Seq<int>)
        requires s.len() > 0
        ensures (s + t).subrange(1, (s + t).len() as int) == s.subrange(1, s.len() as int) + t
    {
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
            /* code modified by LLM (iteration 2): fixed lemma proof by properly establishing the connection between sum_r and sum_l */
            equal_sum_r(s, i, j-1);
            let sub = s.subrange(i, j-1);
            let last = seq![s[(j-1) as int]];
            assert(s.subrange(i, j) == sub + last);
            sum_by_parts_r(sub, last);
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
        let mut sum: i32 = 0;
        let mut i: usize = 0;
        
        /* code modified by LLM (iteration 4): fixed loop invariant and added helper lemma calls */
        while i < v.len()
            invariant 
                0 <= i <= v.len(),
                sum as int == sum_r(v@.subrange(0, i as int).map(|j, x| x as int)),
                sum.abs() <= 100 * v.len()  // overflow prevention
            decreases v.len() - i
        {
            /* code modified by LLM (iteration 4): fixed type casting - access v[i as int] to get proper int type */
            proof {
                let prev_seq = v@.subrange(0, i as int).map(|j, x| x as int);
                let next_seq = v@.subrange(0, (i + 1) as int).map(|j, x| x as int);
                let elem_val = v[i as int] as int;
                assert(next_seq == prev_seq + seq![elem_val]);
                sum_by_parts_r(prev_seq, seq![elem_val]);
            }
            sum = sum + v[i as int];
            i = i + 1;
        }
        /* code modified by LLM (iteration 4): final assertion to connect loop result to postcondition */
        proof {
            assert(v@.subrange(0, v.len() as int) == v@);
        }
        sum
    }

    // Sum elements method - backward iteration (equivalent to Dafny's sumElemsB)
    fn sum_elems_b(v: &[i32]) -> (sum: i32)
        requires v.len() < 100  // Bound to prevent overflow
        ensures sum as int == sum_r(v@.map(|i, x| x as int))
    {
        let mut sum: i32 = 0;
        let mut i: usize = v.len();
        
        /* code modified by LLM (iteration 4): fixed loop invariant and added helper lemma calls */
        while i > 0
            invariant 
                0 <= i <= v.len(),
                sum as int == sum_r(v@.subrange(i as int, v.len() as int).map(|j, x| x as int)),
                sum.abs() <= 100 * v.len()  // overflow prevention
            decreases i
        {
            i = i - 1;
            /* code modified by LLM (iteration 4): fixed type casting - access v[i as int] to get proper int type */
            proof {
                let prev_seq = v@.subrange((i + 1) as int, v.len() as int).map(|j, x| x as int);
                let next_seq = v@.subrange(i as int, v.len() as int).map(|j, x| x as int);
                let elem_val = v[i as int] as int;
                assert(next_seq == seq![elem_val] + prev_seq);
                sum_by_parts_r(seq![elem_val], prev_seq);
            }
            sum = sum + v[i as int];
        }
        /* code modified by LLM (iteration 4): final assertion to connect loop result to postcondition */
        proof {
            assert(v@.subrange(0, v.len() as int) == v@);
        }
        sum
    }
}

fn main() {
    let arr = [1, 2, 3, 4, 5];
    let sum1 = sum_elems(&arr);
    let sum2 = sum_elems_b(&arr);
    println!("Forward sum: {}", sum1);
    println!("Backward sum: {}", sum2);
}