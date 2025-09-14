// Noa Leron 207131871
// Tsuri Farhana 315016907



predicate Sorted(q: seq<int>) {
    forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

/*
Goal: Implement the well known merge sort algorithm in O(a.Length X log_2(a.Length)) time, recursively.

- Divide the contents of the original array into two local arrays
- After sorting the local arrays (recursively), merge the contents of the two returned arrays using the Merge method (see below)
- DO NOT modify the specification or any other part of the method's signature
- DO NOT introduce any further methods
*/

ghost predicate Inv(a: seq<int>, a1: seq<int>, a2: seq<int>, i: nat, mid: nat){
    (i <= |a1|) && (i <= |a2|) && (i+mid <= |a|) &&
    (a1[..i] == a[..i]) && (a2[..i] == a[mid..(i+mid)])
}

/*
Goal: Implement iteratively, correctly, efficiently, clearly

DO NOT modify the specification or any other part of the method's signature
*/
method Merge(b: array<int>, c: array<int>, d: array<int>)
    requires b != c && b != d && b.Length == c.Length + d.Length
    requires Sorted(c[..]) && Sorted(d[..])
    ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
    modifies b
{
  assume{:axiom} false;
}


//This is a method that replace the loop body


//Loop invariant - b is sprted so far and the next two potential values that will go into b are bigger then the biggest value in b.
ghost predicate InvSorted(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
    i <= |c| && j <= |d| && i + j <= |b| &&
    ((i+j > 0 && i < |c|) ==> (b[j + i - 1] <= c[i])) &&
    ((i+j > 0 && j < |d|) ==> (b[j + i - 1] <= d[j])) &&
    Sorted(b[..i+j])
    }


//Loop invariant - the multiset of the prefix of b so far is the same multiset as the prefixes of c and d so far.
ghost predicate InvSubSet(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
    i <= |c| && j <= |d| && i + j <= |b| &&
    multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
}

//This lemma helps dafny see that if the prefixs of arrays are the same multiset until the end of the arrays,
//all the arrays are the same multiset.


//This lemma helps dafny see that after adding the next value from c to b the prefixes are still the same subsets.

// <vc-helpers>
method Merge_Impl(b: array<int>, c: array<int>, d: array<int>)
    requires b != c && b != d && b.Length == c.Length + d.Length
    requires Sorted(c[..]) && Sorted(d[..])
    ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
    modifies b
{
  var i := 0;
  var j := 0;
  ghost var bs: seq<int> := [];
  while i + j < b.Length
    invariant 0 <= i <= c.Length && 0 <= j <= d.Length && i + j <= b.Length
    invariant bs == b[..i+j]
    invariant multiset(bs) == multiset(c[..i]) + multiset(d[..j])
    invariant Sorted(bs)
    invariant (|bs| > 0 && i < c.Length) ==> bs[|bs|-1] <= c[i]
    invariant (|bs| > 0 && j < d.Length) ==> bs[|bs|-1] <= d[j]
  {
    var pos := i + j;
    if i < c.Length && j < d.Length {
      if c[i] <= d[j] {
        b[pos] := c[i];
        bs := bs + [c[i]];
        i := i + 1;
      } else {
        b[pos] := d[j];
        bs := bs + [d[j]];
        j := j + 1;
      }
    } else if i < c.Length {
      b[pos] := c[i];
      bs := bs + [c[i]];
      i := i + 1;
    } else {
      b[pos] := d[j];
      bs := bs + [d[j]];
      j := j + 1;
    }
  }
  // loop finished
  assert i + j == b.Length;
  assert b.Length == c.Length + d.Length;
  assert i + j == c.Length + d.Length;
  assert i <= c.Length && j <= d.Length;
  // derive equalities for i and j
  assert i >= c.Length by {
    calc {
      i;
      == { }
      c.Length + d.Length - j;
      == { }
      c.Length + (d.Length - j);
    }
  }
  assert i == c.Length;
  assert j == d.Length;
  // bs == b[..] and multiset equality from invariant
  assert bs == b[..];
  assert multiset(b[..]) == multiset(c[..i]) + multiset(d[..j]);
  assert multiset(b[..]) == multiset(c[..]) + multiset(d[..]);
  assert Sorted(b[..]);
}
// </vc-helpers>

// <vc-spec>
method MergeSort(a: array<int>) returns (b: array<int>)
    ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
    decreases a.Length
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  if n <= 1 {
    b := new int[n];
    if n == 1 {
      b[0] := a[0];
    }
    return b;
  }
  var mid := n / 2;
  var a1 := new int[mid];
  var a2 := new int[n - mid];
  var i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant forall k :: 0 <= k < i ==> a1[k] == a[k]
  {
    a1[i] := a[i];
    i := i + 1;
  }
  assert a1[..] == a[..mid];
  i := 0;
  while i < n - mid
    invariant 0 <= i <= n - mid
    invariant forall k :: 0 <= k < i ==> a2[k] == a[mid + k]
  {
    a2[i] := a[mid + i];
    i := i + 1;
  }
  assert a2[..] == a[mid..];
  var s1 := MergeSort(a1);
  var s2 := MergeSort(a2);
  b := new int[n];
  Merge_Impl(b, s1, s2);
  // combine recursive postconditions and Merge_Impl postcondition to get final multiset equality
  assert multiset(s1[..]) == multiset(a1[..]);
  assert multiset(s2[..]) == multiset(a2[..]);
  assert multiset(b[..]) == multiset(s1[..]) + multiset(s2[..]);
  assert multiset(b[..]) == multiset(a1[..]) + multiset(a2[..]);
  assert a[..] == a[..mid] + a[mid..];
  assert multiset(a[..]) == multiset(a1[..]) + multiset(a2[..]);
  assert multiset(b[..]) == multiset(a[..]);
  return b;
}
// </vc-code>

