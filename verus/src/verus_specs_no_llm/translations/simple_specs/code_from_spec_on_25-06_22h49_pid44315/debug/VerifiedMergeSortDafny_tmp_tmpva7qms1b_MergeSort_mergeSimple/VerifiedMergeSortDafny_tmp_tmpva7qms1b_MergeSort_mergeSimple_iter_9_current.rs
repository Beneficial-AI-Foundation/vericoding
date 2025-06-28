use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted_seq(a: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

spec fn sorted_slice(a: &Vec<int>, start: int, end: int) -> bool
    requires 0 <= start <= end <= a.len()
{
    forall |i: int, j: int| start <= i < j < end ==> a[i] <= a[j]
}

// Helper spec function to check if all elements of one sequence appear in another
spec fn seq_contains_all(container: Seq<int>, contained: Seq<int>) -> bool {
    forall |i: int| 0 <= i < contained.len() ==> container.contains(contained[i])
}

// Helper lemma for subrange sortedness
proof fn lemma_subrange_sorted(a: Seq<int>, start: int, end: int)
    requires
        sorted_seq(a),
        0 <= start <= end <= a.len()
    ensures
        sorted_seq(a.subrange(start, end))
{
    let sub = a.subrange(start, end);
    assert forall |i: int, j: int| 0 <= i < j < sub.len() implies sub[i] <= sub[j] by {
        assert(sub[i] == a[start + i]);
        assert(sub[j] == a[start + j]);
        assert(start + i < start + j);
        assert(a[start + i] <= a[start + j]);
    }
}

// Lemma to prove that prepending an element maintains sortedness
proof fn lemma_prepend_sorted(elem: int, rest: Seq<int>)
    requires
        sorted_seq(rest),
        rest.len() > 0 ==> elem <= rest[0]
    ensures
        sorted_seq(seq![elem] + rest)
{
    let result = seq![elem] + rest;
    assert forall |i: int, j: int| 0 <= i < j < result.len() implies result[i] <= result[j] by {
        if i == 0 {
            assert(result[0] == elem);
            if j >= 1 && rest.len() > 0 {
                assert(result[j] == rest[j - 1]);
                if j == 1 {
                    assert(elem <= rest[0]);
                    assert(result[j] == rest[0]);
                } else {
                    assert(elem <= rest[0]);
                    assert(0 <= 0 < j - 1 < rest.len());
                    assert(rest[0] <= rest[j - 1]);
                }
            }
        } else {
            assert(i >= 1 && j >= 1);
            assert(result[i] == rest[i - 1]);
            assert(result[j] == rest[j - 1]);
            assert(0 <= i - 1 < j - 1 < rest.len());
            assert(rest[i - 1] <= rest[j - 1]);
        }
    }
}

// Key lemma: when we choose the smaller element, it's <= any element that will appear later
proof fn lemma_merge_order(a1: Seq<int>, a2: Seq<int>, i1: int, i2: int)
    requires
        sorted_seq(a1),
        sorted_seq(a2),
        0 <= i1 < a1.len(),
        0 <= i2 < a2.len(),
        a1[i1] <= a2[i2]
    ensures
        forall |x: int| (a1.subrange(i1 + 1, a1.len() as int).contains(x) || 
                        a2.subrange(i2, a2.len() as int).contains(x)) ==>
                       a1[i1] <= x
{
    assert forall |x: int| (a1.subrange(i1 + 1, a1.len() as int).contains(x) || 
                           a2.subrange(i2, a2.len() as int).contains(x)) implies a1[i1] <= x by {
        if a1.subrange(i1 + 1, a1.len() as int).contains(x) {
            let idx = choose |k: int| i1 + 1 <= k < a1.len() && a1[k] == x;
            assert(i1 < idx);
            assert(a1[i1] <= a1[idx]);
        }
        
        if a2.subrange(i2, a2.len() as int).contains(x) {
            let idx = choose |k: int| i2 <= k < a2.len() && a2[k] == x;
            assert(i2 <= idx);
            assert(a2[i2] <= a2[idx]);
            assert(a1[i1] <= a2[i2]);
            assert(a1[i1] <= x);
        }
    }
}

proof fn lemma_merge_order_2(a1: Seq<int>, a2: Seq<int>, i1: int, i2: int)
    requires
        sorted_seq(a1),
        sorted_seq(a2),
        0 <= i1 < a1.len(),
        0 <= i2 < a2.len(),
        a2[i2] < a1[i1]
    ensures
        forall |x: int| (a1.subrange(i1, a1.len() as int).contains(x) || 
                        a2.subrange(i2 + 1, a2.len() as int).contains(x)) ==>
                       a2[i2] <= x
{
    assert forall |x: int| (a1.subrange(i1, a1.len() as int).contains(x) || 
                           a2.subrange(i2 + 1, a2.len() as int).contains(x)) implies a2[i2] <= x by {
        if a1.subrange(i1, a1.len() as int).contains(x) {
            let idx = choose |k: int| i1 <= k < a1.len() && a1[k] == x;
            assert(i1 <= idx);
            assert(a1[i1] <= a1[idx]);
            assert(a2[i2] < a1[i1]);
            assert(a2[i2] < x);
        }
        
        if a2.subrange(i2 + 1, a2.len() as int).contains(x) {
            let idx = choose |k: int| i2 + 1 <= k < a2.len() && a2[k] == x;
            assert(i2 < idx);
            assert(a2[i2] <= a2[idx]);
        }
    }
}

// Implementation of mergeSimple - merges two sorted sequences
fn mergeSimple(a1: Seq<int>, a2: Seq<int>) -> (result: Seq<int>)
    requires 
        sorted_seq(a1),
        sorted_seq(a2)
    ensures 
        sorted_seq(result),
        result.len() == a1.len() + a2.len(),
        forall |x: int| a1.contains(x) || a2.contains(x) ==> result.contains(x),
        seq_contains_all(result, a1),
        seq_contains_all(result, a2)
{
    let result = merge_recursive(a1, a2, 0, 0);
    
    proof {
        assert(a1.subrange(0, a1.len() as int) =~= a1);
        assert(a2.subrange(0, a2.len() as int) =~= a2);
        
        assert forall |x: int| a1.contains(x) implies result.contains(x) by {
            assert(a1.subrange(0, a1.len() as int).contains(x));
        }
        
        assert forall |x: int| a2.contains(x) implies result.contains(x) by {
            assert(a2.subrange(0, a2.len() as int).contains(x));
        }
    }
    
    result
}

fn merge_recursive(a1: Seq<int>, a2: Seq<int>, i1: int, i2: int) -> (result: Seq<int>)
    requires
        sorted_seq(a1),
        sorted_seq(a2),
        0 <= i1 <= a1.len(),
        0 <= i2 <= a2.len()
    ensures
        sorted_seq(result),
        result.len() == (a1.len() - i1) + (a2.len() - i2),
        forall |x: int| (a1.subrange(i1, a1.len() as int).contains(x) || 
                        a2.subrange(i2, a2.len() as int).contains(x)) ==> result.contains(x),
        seq_contains_all(result, a1.subrange(i1, a1.len() as int)),
        seq_contains_all(result, a2.subrange(i2, a2.len() as int))
    decreases a1.len() - i1 + a2.len() - i2
{
    if i1 >= a1.len() {
        let remaining = a2.subrange(i2, a2.len() as int);
        proof {
            lemma_subrange_sorted(a2, i2, a2.len() as int);
            assert(a1.subrange(i1, a1.len() as int).len() == 0);
        }
        remaining
    } else if i2 >= a2.len() {
        let remaining = a1.subrange(i1, a1.len() as int);
        proof {
            lemma_subrange_sorted(a1, i1, a1.len() as int);
            assert(a2.subrange(i2, a2.len() as int).len() == 0);
        }
        remaining
    } else if a1[i1] <= a2[i2] {
        let rest = merge_recursive(a1, a2, i1 + 1, i2);
        let result = seq![a1[i1]] + rest;
        
        proof {
            if rest.len() > 0 {
                // Use our lemma to show a1[i1] <= all elements that go into rest
                lemma_merge_order(a1, a2, i1, i2);
                
                // Since rest[0] is an element from the merge of remaining parts,
                // and a1[i1] <= all such elements, we have a1[i1] <= rest[0]
                assert(a1[i1] <= rest[0]);
            }
            
            lemma_prepend_sorted(a1[i1], rest);
        }
        
        result
    } else {
        let rest = merge_recursive(a1, a2, i1, i2 + 1);
        let result = seq![a2[i2]] + rest;
        
        proof {
            if rest.len() > 0 {
                // Use our lemma to show a2[i2] <= all elements that go into rest
                lemma_merge_order_2(a1, a2, i1, i2);
                
                // Since rest[0] is an element from the merge of remaining parts,
                // and a2[i2] <= all such elements, we have a2[i2] <= rest[0]
                assert(a2[i2] <= rest[0]);
            }
            
            lemma_prepend_sorted(a2[i2], rest);
        }
        
        result
    }
}

}