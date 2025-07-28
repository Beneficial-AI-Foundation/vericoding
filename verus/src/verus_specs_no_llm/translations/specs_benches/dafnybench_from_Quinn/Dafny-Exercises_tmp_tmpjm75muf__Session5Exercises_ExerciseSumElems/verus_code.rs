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
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Sum elements method - backward iteration (equivalent to Dafny's sumElemsB)
    fn sum_elems_b(v: &[i32]) -> (sum: i32)
        requires v.len() < 100  // Bound to prevent overflow
        ensures sum as int == sum_r(v@.map(|i, x| x as int))
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {
    // TODO: Remove this comment and implement the function body
}