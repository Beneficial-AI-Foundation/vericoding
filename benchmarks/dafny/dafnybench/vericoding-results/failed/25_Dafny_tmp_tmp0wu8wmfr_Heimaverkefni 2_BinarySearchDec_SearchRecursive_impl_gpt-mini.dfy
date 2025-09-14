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

// <vc-helpers>
lemma LeftOfIndexGreater(a: seq<real>, i:int, j:int, m:int, x:real)
  requires 0 <= i <= m < j <= |a|
  requires forall p, q :: i <= p < q < j ==> a[p] >= a[q]
  requires a[m] >= x
  ensures forall r | i <= r < m+1 :: a[r] >= x
{
  var r := i;
  while r < m+1
    invariant i <= r <= m+1
    invariant forall t | i <= t < r :: a[t] >= x
  {
    if r < m {
      assert i <= r < m;
      assert a[r] >= a[m];
      assert a[m] >= x;
      assert a[r] >= x;
    } else {
      // r == m
      assert a[m] >= x;
    }
    r := r + 1;
  }
}

lemma RightOfIndexLess(a: seq<real>, i:int, j:int, m:int, x:real)
  requires 0 <= i <= m < j <= |a|
  requires forall p, q :: i <= p < q < j ==> a[p] >= a[q]
  requires a[m] < x
  ensures forall r | m <= r < j :: a[r] < x
{
  var r := m;
  while r < j
    invariant m <= r <= j
    invariant forall t | m <= t < r :: a[t] < x
  {
    if r == m {
      assert a[m] < x;
    } else {
      assert m < r < j;
      assert a[m] >= a[r];
      assert a[m] < x;
      assert a[r] < x;
    }
    r := r + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    decreases j-i;
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
// </vc-spec>
// <vc-code>
{
  if i == j {
    return i;
  }
  var m := i + (j - i) / 2;
  if a[m] >= x {
    LeftOfIndexGreater(a, i, j, m, x);
    var k := SearchRecursive(a, m+1, j, x);
    assert m+1 <= k <= j;
    assert i <= k <= j;
    var r := i;
    while r < k
      invariant i <= r <= k
      invariant forall t | i <= t < r :: a[t] >= x
    {
      if r < m+1 {
        assert i <= r < m+1;
        assert a[r] >= x;
      } else {
        assert m+1 <= r < k;
        assert a[r] >= x;
      }
      r := r + 1;
    }
    return k;
  } else {
    RightOfIndexLess(a, i, j, m, x);
    var k := SearchRecursive(a, i, m, x);
    assert i <= k <= m;
    var r := k;
    while r < j
      invariant k <= r <= j
      invariant forall t | k <= t < r :: a[t] < x
    {
      if r < m {
        assert k <= r < m;
        assert a[r] < x;
      } else {
        assert m <= r < j;
        assert a[r] < x;
      }
      r := r + 1;
    }
    return k;
  }
}
// </vc-code>

// Ef eftirfarandi fall er ekki samþykkt þá eru
// föllin ekki að haga sér rétt að mati Dafny.