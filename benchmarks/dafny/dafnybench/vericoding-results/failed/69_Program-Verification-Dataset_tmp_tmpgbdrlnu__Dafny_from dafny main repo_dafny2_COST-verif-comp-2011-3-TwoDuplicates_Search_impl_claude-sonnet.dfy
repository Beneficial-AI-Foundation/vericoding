// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


/*
Rustan Leino, 5 Oct 2011

COST Verification Competition, Challenge 3: Two equal elements
http://foveoos2011.cost-ic0701.org/verification-competition

Given: An integer array a of length n+2 with n>=2. It is known that at
least two values stored in the array appear twice (i.e., there are at
least two duplets).

Implement and verify a program finding such two values.

You may assume that the array contains values between 0 and n-1.
*/

// Remarks:

// The implementation of method 'Search' takes one pass through the elements of
// the given array.  To keep track of what it has seen, it allocates an array as
// temporary storage--I imagine that this is what the competition designers
// had in mind, since the problem description says one can assume the values
// of the given array to lie in the range 0..n.

// To keep track of whether it already has found one duplicate, the method
// sets the output variables p and q as follows:
//   p != q   - no duplicates found yet
//   p == q   - one duplicate found so far, namely the value stored in p and q
// Note, the loop invariant does not need to say anything about the state
// of two duplicates having been found, because when the second duplicate is
// found, the method returns.

// What needs to be human-trusted about this program is the specification of
// 'Search'.  The specification straightforwardly lists the assumptions stated
// in the problem description, including the given fact that the array contains
// (at least) two distinct elements that each occurs (at least) twice.  To
// trust the specification of 'Search', a human also needs to trust the definition
// of 'IsDuplicate' and its auxiliary function 'IsPrefixDuplicate'.

// About Dafny:
// As always (when it is successful), Dafny verifies that the program does not
// cause any run-time errors (like array index bounds errors), that the program
// terminates, that expressions and functions are well defined, and that all
// specifications are satisfied.  The language prevents type errors by being type
// safe, prevents dangling pointers by not having an "address-of" or "deallocate"
// operation (which is accommodated at run time by a garbage collector), and
// prevents arithmetic overflow errors by using mathematical integers (which
// is accommodated at run time by using BigNum's).  By proving that programs
// terminate, Dafny proves that a program's time usage is finite, which implies
// that the program's space usage is finite too.  However, executing the
// program may fall short of your hopes if you don't have enough time or
// space; that is, the program may run out of space or may fail to terminate in
// your lifetime, because Dafny does not prove that the time or space needed by
// the program matches your execution environment.  The only input fed to
// the Dafny verifier/compiler is the program text below; Dafny then automatically
// verifies and compiles the program (for this program in less than 11 seconds)
// without further human intervention.

ghost predicate IsDuplicate(a: array<int>, p: int)
  reads a
{
  IsPrefixDuplicate(a, a.Length, p)
}

ghost predicate IsPrefixDuplicate(a: array<int>, k: int, p: int)
  requires 0 <= k <= a.Length;
  reads a;
{
  exists i,j :: 0 <= i < j < k && a[i] == a[j] == p
}

// <vc-helpers>
lemma IsPrefixDuplicateMonotonic(a: array<int>, k: int, k': int, p: int)
  requires 0 <= k <= k' <= a.Length
  requires IsPrefixDuplicate(a, k, p)
  ensures IsPrefixDuplicate(a, k', p)
{
  var i, j :| 0 <= i < j < k && a[i] == a[j] == p;
  assert 0 <= i < j < k' && a[i] == a[j] == p;
}

lemma IsPrefixDuplicateExtend(a: array<int>, k: int, p: int)
  requires 0 <= k <= a.Length
  requires IsPrefixDuplicate(a, k, p)
  ensures IsDuplicate(a, p)
{
  IsPrefixDuplicateMonotonic(a, k, a.Length, p);
}

lemma SetSeenPreservesInvariant(a: array<int>, seen: array<bool>, i: int, val: int, n: int)
  requires 0 <= i < a.Length
  requires 0 <= val < n
  requires seen.Length == n
  requires a[i] == val
  requires !seen[val]
  requires forall j :: 0 <= j < n ==> seen[j] <==> exists k :: 0 <= k < i && a[k] == j
  ensures forall j :: 0 <= j < n ==> (if j == val then true else seen[j]) <==> exists k :: 0 <= k < i + 1 && a[k] == j
{
  forall j | 0 <= j < n
    ensures (if j == val then true else seen[j]) <==> exists k :: 0 <= k < i + 1 && a[k] == j
  {
    if j == val {
      assert a[i] == j;
      assert exists k :: 0 <= k < i + 1 && a[k] == j;
    } else {
      if seen[j] {
        var k :| 0 <= k < i && a[k] == j;
        assert 0 <= k < i + 1 && a[k] == j;
      }
      if exists k :: 0 <= k < i + 1 && a[k] == j {
        var k :| 0 <= k < i + 1 && a[k] == j;
        if k == i {
          assert a[k] == val;
          assert j == val;
          assert false;
        } else {
          assert 0 <= k < i && a[k] == j;
        }
      }
    }
  }
}

lemma FindDuplicatePreservesInvariant(a: array<int>, seen: array<bool>, i: int, val: int, n: int, oldP: int, oldQ: int)
  requires 0 <= i < a.Length
  requires 0 <= val < n
  requires seen.Length == n
  requires a[i] == val
  requires seen[val]
  requires forall j :: 0 <= j < n ==> seen[j] <==> exists k :: 0 <= k < i && a[k] == j
  requires (oldP != oldQ) ==> !exists x :: IsPrefixDuplicate(a, i, x)
  ensures forall j :: 0 <= j < n ==> seen[j] <==> exists k :: 0 <= k < i + 1 && a[k] == j
  ensures oldP != oldQ ==> IsPrefixDuplicate(a, i + 1, val)
{
  forall j | 0 <= j < n
    ensures seen[j] <==> exists k :: 0 <= k < i + 1 && a[k] == j
  {
    if seen[j] {
      var k :| 0 <= k < i && a[k] == j;
      assert 0 <= k < i + 1 && a[k] == j;
    }
    if exists k :: 0 <= k < i + 1 && a[k] == j {
      var k :| 0 <= k < i + 1 && a[k] == j;
      if k == i {
        assert a[k] == val;
        assert j == val;
        assert seen[j];
      } else {
        assert 0 <= k < i && a[k] == j;
        assert seen[j];
      }
    }
  }
  
  if oldP != oldQ {
    var k :| 0 <= k < i && a[k] == val;
    assert 0 <= k < i < i + 1 && a[k] == a[i] == val;
    assert IsPrefixDuplicate(a, i + 1, val);
  }
}

lemma InitialSeenState(seen: array<bool>, n: int)
  requires seen.Length == n
  requires forall j :: 0 <= j < n ==> !seen[j]
  ensures forall j :: 0 <= j < n ==> seen[j] <==> exists k :: 0 <= k < 0 && false
{
  forall j | 0 <= j < n
    ensures seen[j] <==> exists k :: 0 <= k < 0 && false
  {
    assert !seen[j];
    assert !(exists k :: 0 <= k < 0 && false);
  }
}
// </vc-helpers>

// <vc-spec>
method Search(a: array<int>) returns (p: int, q: int)
  requires 4 <= a.Length;
  requires exists p,q :: p != q && IsDuplicate(a, p) && IsDuplicate(a, q);  // two distinct duplicates exist
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] < a.Length - 2;  // the elements of "a" in the range [0.. a.Length-2]
  ensures p != q && IsDuplicate(a, p) && IsDuplicate(a, q);
// </vc-spec>
// <vc-code>
{
  var n := a.Length - 2;
  var seen := new bool[n];
  var i := 0;
  p := 0;
  q := 1;
  
  InitialSeenState(seen, n);
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant seen.Length == n
    invariant forall j :: 0 <= j < i ==> 0 <= a[j] < n
    invariant forall j :: 0 <= j < n ==> seen[j] <==> exists k :: 0 <= k < i && a[k] == j
    invariant (p == q) ==> IsPrefixDuplicate(a, i, p)
    invariant (p != q) ==> !exists x :: IsPrefixDuplicate(a, i, x)
  {
    var val := a[i];
    assert 0 <= val < n;
    
    if seen[val] {
      if p == q {
        if val != p {
          var oldP := p;
          var oldQ := q;
          q := val;
          assert forall j :: 0 <= j < n ==> seen[j] <==> exists k :: 0 <= k < i && a[k] == j;
          FindDuplicatePreservesInvariant(a, seen, i, val, n, oldP, oldQ);
          IsPrefixDuplicateExtend(a, i + 1, p);
          IsPrefixDuplicateExtend(a, i + 1, q);
          return;
        }
      } else {
        var oldP := p;
        var oldQ := q;
        assert forall j :: 0 <= j < n ==> seen[j] <==> exists k :: 0 <= k < i && a[k] == j;
        FindDuplicatePreservesInvariant(a, seen, i, val, n, oldP, oldQ);
        p := val;
        q := val;
      }
    } else {
      seen[val] := true;
      SetSeenPreservesInvariant(a, seen, i, val, n);
    }
    
    i := i + 1;
  }
  
  assert false;
}
// </vc-code>

