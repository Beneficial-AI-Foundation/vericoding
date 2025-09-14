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
ghost predicate HasDuplicateUpTo(a: array<int>, idx: int, value: int)
  requires 0 <= idx <= a.Length
  reads a
{
  exists i, j :: 0 <= i < j < idx && a[i] == a[j] == value
}

lemma LemmaUniqueDuplicate(a: array<int>, idx: int, x: int, y: int)
  requires 0 <= idx <= a.Length
  requires x != y
  requires HasDuplicateUpTo(a, idx, x)
  requires HasDuplicateUpTo(a, idx, y)
  ensures IsDuplicate(a, x) && IsDuplicate(a, y)
{
}

lemma LemmaExtendDuplicate(a: array<int>, idx: int, value: int)
  requires 0 <= idx < a.Length
  requires exists j :: 0 <= j < idx && a[j] == a[idx]
  ensures HasDuplicateUpTo(a, idx + 1, value) <==> value == a[idx] || HasDuplicateUpTo(a, idx, value)
{
}

lemma LemmaInitialInvariants(a: array<int>, seen: array<int>, n: int, i: int)
  requires a != null && seen != null
  requires 0 <= i <= n
  requires n == a.Length == seen.Length
  requires forall k :: 0 <= k < n ==> seen[k] == 0
  ensures forall x :: 0 <= x < n ==> seen[x] == 0 || seen[x] == 1 || seen[x] == 2
  ensures forall x :: 0 <= x < n ==> seen[x] == 1 ==> exists j :: 0 <= j < i && a[j] == x
  ensures forall x :: 0 <= x < n ==> seen[x] == 2 ==> HasDuplicateUpTo(a, i, x)
{
}

lemma LemmaUpdateInvariants(a: array<int>, seen: array<int>, n: int, i: int, value: int, seenOld: seq<int>)
  requires a != null && seen != null
  requires 0 <= i < n
  requires n == a.Length == seen.Length
  requires value == a[i]
  requires 0 <= value < n
  requires forall x :: 0 <= x < n ==> seenOld[x] == 0 || seenOld[x] == 1 || seenOld[x] == 2
  requires forall x :: 0 <= x < n ==> seenOld[x] == 1 ==> exists j :: 0 <= j < i && a[j] == x
  requires forall x :: 0 <= x < n ==> seenOld[x] == 2 ==> HasDuplicateUpTo(a, i, x)
  requires seen[value] == (if seenOld[value] == 0 then 1 else 2)
  requires forall x :: 0 <= x < n && x != value ==> seen[x] == seenOld[x]
  ensures forall x :: 0 <= x < n ==> seen[x] == 0 || seen[x] == 1 || seen[x] == 2
  ensures forall x :: 0 <= x < n ==> seen[x] == 1 ==> exists j :: 0 <= j < i+1 && a[j] == x
  ensures forall x :: 0 <= x < n ==> seen[x] == 2 ==> HasDuplicateUpTo(a, i+1, x)
{
}

lemma LemmaFindSecondDuplicate(a: array<int>, p: int) returns (q: int)
  requires IsDuplicate(a, p)
  requires exists q :: q != p && IsDuplicate(a, q)
  ensures q != p && IsDuplicate(a, q)
{
  var r := 0;
  while r < a.Length
    invariant 0 <= r <= a.Length
    invariant forall s :: 0 <= s < r ==> s == p || !IsDuplicate(a, s)
  {
    if r != p && IsDuplicate(a, r) {
      q := r;
      return;
    }
    r := r + 1;
  }
  assert false;
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
  var n := a.Length;
  var seen := new int[n];
  var i := 0;
  p := -1;
  q := -1;
  
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall x :: 0 <= x < n ==> seen[x] == 0
  {
    seen[k] := 0;
    k := k + 1;
  }
  
  LemmaInitialInvariants(a, seen, n, i);
  
  while i < n
    invariant 0 <= i <= n
    invariant p != q || p == -1
    invariant p != -1 ==> HasDuplicateUpTo(a, i, p)
    invariant q != -1 ==> HasDuplicateUpTo(a, i, q)
    invariant forall x :: 0 <= x < n ==> seen[x] == 0 || seen[x] == 1 || seen[x] == 2
    invariant forall x :: 0 <= x < n ==> seen[x] == 1 ==> exists j :: 0 <= j < i && a[j] == x
    invariant forall x :: 0 <= x < n ==> seen[x] == 2 ==> HasDuplicateUpTo(a, i, x)
  {
    var value := a[i];
    var seenOld := seen[..];
    
    if seen[value] == 0 {
      seen[value] := 1;
    } else if seen[value] == 1 {
      seen[value] := 2;
      if p == -1 {
        p := value;
      } else if value != p {
        q := value;
        break;
      }
    }
    
    LemmaUpdateInvariants(a, seen, n, i, value, seenOld);
    i := i + 1;
  }
  
  if q == -1 {
    q := LemmaFindSecondDuplicate(a, p);
  }
}
// </vc-code>

