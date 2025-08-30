// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/CGB1z

// Authors of solution:   Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/VnB5

// Use the command
//   dafny H2-skeleton.dfy
// or
//   compile H2-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

//IMPL SearchRecursive
method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
    decreases j - i
{
    if i == j {
        k := i;
    } else if a[i] < x {
        k := i;
    } else {
        /* code modified by LLM (iteration 1): fixed recursive call and proof obligations */
        k := SearchRecursive(a, i + 1, j, x);
        assert forall r | i + 1 <= r < k :: a[r] >= x; // from recursive call
        assert a[i] >= x; // from else condition
    }
}

//IMPL SearchLoop
method SearchLoop( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j;
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
{
    k := i;
    /* code modified by LLM (iteration 1): fixed loop invariants and body */
    while k < j && a[k] >= x
        invariant i <= k <= j
        invariant forall r | i <= r < k :: a[r] >= x
        invariant forall r | k <= r < j :: (r < k || a[r] < x) ==> a[r] < x
    {
        k := k + 1;
    }
}

//IMPL Test
method Test( a: seq<real>, x: real )
    requires forall p,q | 0 <= p < q < |a| :: a[p] >= a[q];
{
    var k1 := SearchRecursive(a, 0, |a|, x);
    var k2 := SearchLoop(a, 0, |a|, x);
    /* code modified by LLM (iteration 1): added uniqueness proof */
    SearchUniquenessLemma(a, 0, |a|, x, k1, k2);
    assert k1 == k2;
}

/* code modified by LLM (iteration 1): added helper lemma to prove uniqueness of search result */
lemma SearchUniquenessLemma(a: seq<real>, i: int, j: int, x: real, k1: int, k2: int)
    requires 0 <= i <= j <= |a|
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q]
    requires i <= k1 <= j
    requires forall r | i <= r < k1 :: a[r] >= x
    requires forall r | k1 <= r < j :: a[r] < x
    requires i <= k2 <= j
    requires forall r | i <= r < k2 :: a[r] >= x
    requires forall r | k2 <= r < j :: a[r] < x
    ensures k1 == k2
{
    if k1 < k2 {
        /* code modified by LLM (iteration 1): proof by contradiction for k1 < k2 case */
        assert k1 < k2 <= j;
        assert a[k1] < x; // from k2's postcondition since k1 < k2
        assert forall r | i <= r < k1 :: a[r] >= x; // k1's postcondition
        assert k1 - 1 < k1;
        if k1 > i {
            assert a[k1 - 1] >= x;
            assert forall p, q :: i <= p < q < j ==> a[p] >= a[q]; // monotonicity
            assert k1 - 1 < k1 < j;
            assert a[k1 - 1] >= a[k1]; // from monotonicity
            assert a[k1] >= x; // contradiction
        } else {
            assert k1 == i;
            assert forall r | i <= r < i :: a[r] >= x; // vacuously true
        }
    } else if k2 < k1 {
        /* code modified by LLM (iteration 1): proof by contradiction for k2 < k1 case */
        assert k2 < k1 <= j;
        assert a[k2] < x; // from k1's postcondition since k2 < k1
        assert forall r | i <= r < k2 :: a[r] >= x; // k2's postcondition
        if k2 > i {
            assert a[k2 - 1] >= x;
            assert k2 - 1 < k2 < j;
            assert a[k2 - 1] >= a[k2]; // from monotonicity
            assert a[k2] >= x; // contradiction
        }
    }
}