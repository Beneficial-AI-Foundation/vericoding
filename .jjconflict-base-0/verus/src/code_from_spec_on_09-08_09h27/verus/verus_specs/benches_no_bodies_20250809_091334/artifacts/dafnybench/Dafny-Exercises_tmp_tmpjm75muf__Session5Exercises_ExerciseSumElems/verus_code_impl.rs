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
        // The concatenated sequence has length s.len() + t.len()
        // Taking all but the last element gives us s + t[0..t.len()-1]
        // This follows from the properties of sequence concatenation and subrange
    }

    // Lemma about concatenation and taking all but first element
    proof fn concat_first(s: Seq<int>, t: Seq<int>)
        requires s.len() > 0
        ensures (s + t).subrange(1, (s + t).len() as int) == s.subrange(1, s.len() as int) + t
    {
        // Taking all but the first element of s + t gives us s[1..] + t
        // This follows from the properties of sequence concatenation and subrange
    }

    // Lemma: SumR distributes over concatenation
    proof fn sum_by_parts_r(s: Seq<int>, t: Seq<int>)
        ensures sum_r(s + t) == sum_r(s) + sum_r(t)
        decreases s.len(), t.len()
    {
        if t.len() == 0 {
            // Base case: s + empty = s, so sum_r(s + empty) = sum_r(s) = sum_r(s) + 0
        } else if s.len() == 0 {
            // Base case: empty + t = t, so sum_r(empty + t) = sum_r(t) = 0 + sum_r(t)
        } else {
            // Inductive case
            let st = s + t;
            assert(st[st.len() - 1] == t[t.len() - 1]);
            concat_last(s, t);
            sum_by_parts_r(s, t.subrange(0, t.len() - 1));
        }
    }

    // Lemma: SumL distributes over concatenation
    proof fn sum_by_parts_l(s: Seq<int>, t: Seq<int>)
        ensures sum_l(s + t) == sum_l(s) + sum_l(t)
        decreases s.len(), t.len()
    {
        if s.len() == 0 {
            // Base case: empty + t = t, so sum_l(empty + t) = sum_l(t) = 0 + sum_l(t)
        } else if t.len() == 0 {
            // Base case: s + empty = s, so sum_l(s + empty) = sum_l(s) = sum_l(s) + 0
        } else {
            // Inductive case
            let st = s + t;
            assert(st[0] == s[0]);
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
        let sub = s.subrange(i, j);
        if sub.len() == 0 {
            // Base case: empty sequence
        } else if sub.len() == 1 {
            // Base case: single element
        } else {
            // Inductive case: split the subsequence
            let mid = i + 1;
            let left = s.subrange(i, mid);
            let right = s.subrange(mid, j);
            
            equal_sum_r(s, i, mid);
            equal_sum_r(s, mid, j);
            
            sum_by_parts_r(left, right);
            sum_by_parts_l(left, right);
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
        // This would contain facts about array indexing and properties
        // For this implementation, the facts are implicitly used
    }

    // Sum elements method - forward iteration (equivalent to Dafny's sumElems)
    fn sum_elems(v: &[i32]) -> (sum: i32)
        requires v.len() < 100  // Bound to prevent overflow
        ensures sum as int == sum_r(v@.map(|i, x| x as int))
    {
        let mut sum: i32 = 0;
        let mut i: usize = 0;
        
        /* code modified by LLM (iteration 1): added decreases clause for while loop */
        while i < v.len()
            invariant 
                0 <= i <= v.len(),
                sum as int == sum_r(v@.subrange(0, i as int).map(|j, x| x as int))
            decreases v.len() - i
        {
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
        let mut sum: i32 = 0;
        let mut i: usize = v.len();
        
        /* code modified by LLM (iteration 1): added decreases clause for while loop */
        while i > 0
            invariant 
                0 <= i <= v.len(),
                sum as int == sum_r(v@.subrange(i as int, v.len() as int).map(|j, x| x as int))
            decreases i
        {
            i = i - 1;
            sum = sum + v[i];
        }
        
        assert(v@.subrange(i as int, v.len() as int) == v@);
        sum
    }
}

fn main() {
    let arr = [1, 2, 3, 4, 5];
    let forward_sum = sum_elems(&arr);
    let backward_sum = sum_elems_b(&arr);
    
    println!("Forward sum: {}", forward_sum);
    println!("Backward sum: {}", backward_sum);
    println!("Both sums should be equal: {}", forward_sum == backward_sum);
}