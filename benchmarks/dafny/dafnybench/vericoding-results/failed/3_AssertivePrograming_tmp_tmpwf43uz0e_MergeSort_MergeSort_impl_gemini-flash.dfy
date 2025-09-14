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
lemma LemmaSortedPrefixMergeC(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
    requires Sorted(b[..i+j])
    requires i < |c|
    requires forall k :: 0 <= k < i+j ==> b[k] <= c[i] // This line is new
    ensures Sorted(b[..i+j] + [c[i]])
{
}

lemma LemmaSortedPrefixMergeD(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
    requires Sorted(b[..i+j])
    requires j < |d|
    requires forall k :: 0 <= k < i+j ==> b[k] <= d[j] // This line is new
    ensures Sorted(b[..i+j] + [d[j]])
{
}

lemma LemmaMultiset(s1: seq<int>, s2: seq<int>)
    requires multiset(s1) == multiset(s2)
    ensures |s1| == |s2|
{}

lemma MergeLemma(b: seq<int>, c: seq<int>, d: seq<int>)
    requires multiset(b) == multiset(c) + multiset(d)
    requires |b| == |c| + |d|
    ensures multiset(b) == multiset(c) + multiset(d)
{}
method Merge(b: array<int>, c: array<int>, d: array<int>)
    requires b != c && b != d && b.Length == c.Length + d.Length
    requires Sorted(c[..]) && Sorted(d[..])
    ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
    modifies b
{
  var i := 0;
  var j := 0;
  while i < c.Length || j < d.Length
    invariant 0 <= i <= c.Length
    invariant 0 <= j <= d.Length
    invariant i + j <= b.Length
    invariant Sorted(b[..i+j])
    invariant multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
  {
    if i < c.Length && (j == d.Length || c[i] <= d[j]) {
      b[i+j] := c[i];
      if i+j > 0 {
          LemmaSortedPrefixMergeC(b[..i+j], c[..], d[..], i, j);
      }
      i := i + 1;
    } else {
      b[i+j] := d[j];
      if i+j > 0 {
          LemmaSortedPrefixMergeD(b[..i+j], c[..], d[..], i, j);
      }
      j := j + 1;
    }
  }
  MergeLemma(b[..], c[..], d[..]);
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
    b := new int[a.Length];
    if a.Length == 1 {
        b[0] := a[0];
    }
    return b;
  }

  var mid := a.Length / 2;

  var b1_arr := new int[mid];
  var b2_arr := new int[a.Length - mid];

  // Populate b1_arr
  forall k | 0 <= k < mid {
    b1_arr[k] := a[k];
  }

  // Populate b2_arr
  forall k | 0 <= k < a.Length - mid {
    b2_arr[k] := a[mid + k];
  }

  var sorted_b1 := MergeSort(b1_arr);
  var sorted_b2 := MergeSort(b2_arr);

  b := new int[a.Length];
  Merge(b, sorted_b1, sorted_b2);
  return b;
}
// </vc-code>

