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
lemma SeqSplit<T>(s: seq<T>, i: nat)
  requires i <= |s|
  ensures s == s[..i] + s[i..]
{
}

lemma MultisetSplit<T>(s: seq<T>, i: nat)
  requires i <= |s|
  ensures multiset(s) == multiset(s[..i]) + multiset(s[i..])
{
  SeqSplit(s, i);
}
// </vc-helpers>

// <vc-spec>
method MergeSort(a: array<int>) returns (b: array<int>)
    ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
    decreases a.Length
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 {
    b := a;
  } else {
    var mid := a.Length / 2;
    var c := new int[mid];
    var d := new int[a.Length - mid];

    var i := 0;
    while i < mid
      invariant 0 <= i <= mid
      invariant c[..i] == a[..i]
    {
      c[i] := a[i];
      i := i + 1;
    }
    assert i == mid;
    assert c.Length == mid;
    assert i == c.Length;
    assert c[..] == c[..i];
    assert c[..i] == a[..i];
    assert a[..i] == a[..mid];
    assert c[..] == a[..mid];

    var j := 0;
    while j < a.Length - mid
      invariant 0 <= j <= a.Length - mid
      invariant d[..j] == a[mid..mid+j]
    {
      d[j] := a[mid + j];
      j := j + 1;
    }
    assert j == a.Length - mid;
    assert d.Length == a.Length - mid;
    assert j == d.Length;
    assert d[..] == d[..j];
    assert d[..j] == a[mid..mid+j];
    assert mid + j == a.Length;
    assert a[mid..mid+j] == a[mid..];
    assert d[..] == a[mid..];

    var cs := MergeSort(c);
    var ds := MergeSort(d);

    b := new int[a.Length];

    Merge(b, cs, ds);

    assert multiset(b[..]) == multiset(cs[..]) + multiset(ds[..]);
    assert multiset(cs[..]) == multiset(c[..]);
    assert multiset(ds[..]) == multiset(d[..]);
    assert multiset(b[..]) == multiset(c[..]) + multiset(d[..]);

    assert c[..] == a[..mid];
    assert d[..] == a[mid..];
    assert multiset(b[..]) == multiset(a[..mid]) + multiset(a[mid..]);

    assert 0 <= mid <= a.Length;
    MultisetSplit(a[..], mid);
    assert multiset(a[..]) == multiset(a[..mid]) + multiset(a[mid..]);

    assert multiset(a[..]) == multiset(b[..]);
  }
}
// </vc-code>

