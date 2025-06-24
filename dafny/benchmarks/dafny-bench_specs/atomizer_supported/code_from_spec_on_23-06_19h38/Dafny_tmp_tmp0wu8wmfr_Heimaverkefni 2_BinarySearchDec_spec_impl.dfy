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
{
    if i == j {
        k := i;
    } else if a[i] < x {
        k := i;
        /* code modified by LLM (iteration 4): Added assertion and lemma call to establish postcondition */
        assert a[i] < x;
        MonotonicityLemma(a, i, j, i, x);
    } else {
        k := SearchRecursive(a, i + 1, j, x);
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
    while k < j && a[k] >= x
        invariant i <= k <= j;
        invariant forall r | i <= r < k :: a[r] >= x;
    {
        k := k + 1;
    }
    /* code modified by LLM (iteration 4): Added helper lemma call to establish postcondition */
    if k < j {
        assert a[k] < x;
        MonotonicityLemma(a, i, j, k, x);
    }
}

/* code modified by LLM (iteration 4): Fixed helper lemma preconditions and logic */
lemma MonotonicityLemma(a: seq<real>, i: int, j: int, k: int, x: real)
    requires 0 <= i <= k < j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    requires a[k] < x;
    ensures forall r | k <= r < j :: a[r] < x;
{
    forall r | k <= r < j 
        ensures a[r] < x;
    {
        if r == k {
            assert a[r] < x;
        } else {
            assert k < r < j;
            assert a[k] >= a[r];
            assert a[r] <= a[k] < x;
        }
    }
}

/* code modified by LLM (iteration 4): Helper lemma for uniqueness proof */
lemma SearchUniqueness(a: seq<real>, i: int, j: int, x: real, k1: int, k2: int)
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    requires i <= k1 <= j;
    requires forall r | i <= r < k1 :: a[r] >= x;
    requires forall r | k1 <= r < j :: a[r] < x;
    requires i <= k2 <= j;
    requires forall r | i <= r < k2 :: a[r] >= x;
    requires forall r | k2 <= r < j :: a[r] < x;
    ensures k1 == k2;
{
    if k1 != k2 {
        if k1 < k2 {
            assert a[k1] < x;
            assert a[k1] >= x;
            assert false;
        } else {
            assert a[k2] < x;
            assert a[k2] >= x;
            assert false;
        }
    }
}

//IMPL Test
method Test( a: seq<real>, x: real )
    requires forall p,q | 0 <= p < q < |a| :: a[p] >= a[q];
{
    if |a| > 0 {
        var k1 := SearchRecursive(a, 0, |a|, x);
        var k2 := SearchLoop(a, 0, |a|, x);
        /* code modified by LLM (iteration 4): Added lemma call to prove k1 == k2 */
        SearchUniqueness(a, 0, |a|, x, k1, k2);
        assert k1 == k2;
    }
}