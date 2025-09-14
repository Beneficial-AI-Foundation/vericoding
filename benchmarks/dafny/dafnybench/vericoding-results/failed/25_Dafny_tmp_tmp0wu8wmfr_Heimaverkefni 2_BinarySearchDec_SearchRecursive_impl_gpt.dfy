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
// no helpers needed
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
    k := i;
    return;
  }
  if a[i] < x {
    k := i;
    assert forall r | k <= r < j :: a[r] < x by {
      forall r | k <= r < j {
        assert k == i;
        if r == i {
          assert a[r] < x;
        } else {
          assert i < r < j;
          assert i <= i < r < j;
          assert a[i] >= a[r];
          assert a[r] < x;
        }
      }
    }
    return;
  } else {
    assert 0 <= i + 1 <= j;
    assert forall p, q :: i + 1 <= p < q < j ==> a[p] >= a[q] by {
      forall p, q | i + 1 <= p < q < j {
        assert i <= p < q < j;
      }
    }
    var k2 := SearchRecursive(a, i + 1, j, x);
    k := k2;
    assert forall r | i <= r < k :: a[r] >= x by {
      forall r | i <= r < k {
        if r == i {
          assert a[i] >= x;
        } else {
          assert i + 1 <= r < k;
          assert a[r] >= x;
        }
      }
    }
    return;
  }
}
// </vc-code>

// Ef eftirfarandi fall er ekki samþykkt þá eru
// föllin ekki að haga sér rétt að mati Dafny.