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

// <vc-helpers>
lemma MultisetConcatenation(a: seq<int>, mid: int)
    requires 0 <= mid <= |a|
    ensures multiset(a[..]) == multiset(a[..mid]) + multiset(a[mid..])
{
    if mid == 0 {
        assert a[..mid] == [];
        assert a[mid..] == a[..];
    } else if mid == |a| {
        assert a[..mid] == a[..];
        assert a[mid..] == [];
    } else {
        assert a[..] == a[..mid] + a[mid..];
    }
}

lemma ArrayCopyPreservesMultiset(original: array<int>, copy: array<int>, start: int, len: int)
    requires 0 <= start && start + len <= original.Length
    requires copy.Length == len
    requires forall k :: 0 <= k < len ==> copy[k] == original[start + k]
    ensures multiset(copy[..]) == multiset(original[start..start+len])
{
    if len == 0 {
        assert copy[..] == [];
        assert original[start..start+len] == [];
    } else {
        var i := 0;
        while i < len
            invariant 0 <= i <= len
            invariant copy[..i] == original[start..start+i]
        {
            i := i + 1;
        }
        assert copy[..] == original[start..start+len];
    }
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
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant b[..i] == a[..i]
      modifies b
    {
      b[i] := a[i];
      i := i + 1;
    }
    return;
  }
  
  var mid := a.Length / 2;
  var left := new int[mid];
  var right := new int[a.Length - mid];
  
  var i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant left[..i] == a[..i]
    modifies left
  {
    left[i] := a[i];
    i := i + 1;
  }
  
  i := 0;
  while i < a.Length - mid
    invariant 0 <= i <= a.Length - mid
    invariant right[..i] == a[mid..mid+i]
    modifies right
  {
    right[i] := a[mid + i];
    i := i + 1;
  }
  
  // Prove that the arrays contain the right elements
  assert left[..] == a[..mid];
  assert right[..] == a[mid..];
  
  // Use the helper lemma to establish multiset equality
  ArrayCopyPreservesMultiset(a, left, 0, mid);
  ArrayCopyPreservesMultiset(a, right, mid, a.Length - mid);
  
  MultisetConcatenation(a[..], mid);
  assert multiset(a[..]) == multiset(left[..]) + multiset(right[..]);
  
  var sortedLeft := MergeSort(left);
  var sortedRight := MergeSort(right);
  
  // From postconditions of recursive calls:
  // multiset(left[..]) == multiset(sortedLeft[..])
  // multiset(right[..]) == multiset(sortedRight[..])
  assert multiset(a[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
  
  b := new int[a.Length];
  Merge(b, sortedLeft, sortedRight);
  
  // From postcondition of Merge:
  // multiset(b[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..])
  assert multiset(a[..]) == multiset(b[..]);
}
// </vc-code>

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
    var i: nat, j: nat := 0, 0;
    while i + j < b.Length
        invariant i <= c.Length && j <= d.Length && i + j <= b.Length
        invariant i + j < b.Length ==> (i < c.Length || j < d.Length)
        invariant multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
        invariant Sorted(b[..i+j])
        invariant i + j > 0 && i < c.Length ==> b[i+j-1] <= c[i]
        invariant i + j > 0 && j < d.Length ==> b[i+j-1] <= d[j]
        decreases c.Length + d.Length - i - j
    {   
        if i == c.Length {
            b[i + j] := d[j];
            j := j + 1;
        } else if j == d.Length {
            b[i + j] := c[i];
            i := i + 1;
        } else if c[i] <= d[j] {
            b[i + j] := c[i];
            i := i + 1;
        } else {
            b[i + j] := d[j];
            j := j + 1;
        }
    }
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
lemma LemmaMultysetsEquals (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
    requires i == |c|
    requires j == |d|
    requires i + j == |b|
    requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
    ensures multiset(b[..]) == multiset(c[..])+multiset(d[..])
    {
        assert b[..] == b[..i+j];
        assert c[..] == c[..i];
        assert d[..] == d[..j];
    }


//This lemma helps dafny see that after adding the next value from c to b the prefixes are still the same subsets.
lemma lemmaInvSubsetTakeValueFromC (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
    requires i < |c|
    requires j <= |d|
    requires i + j < |b|
    requires |c| + |d| == |b|
    requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
    requires b[i+j] == c[i]
    ensures multiset(b[..i+j+1]) == multiset(c[..i+1])+multiset(d[..j])
    {
        assert c[..i]+[c[i]] == c[..i+1];
        assert b[..i+j+1] == b[..i+j] + [b[i+j]];
        assert multiset(b[..i+j+1]) == multiset(c[..i+1])+multiset(d[..j]);
    }



//This lemma helps dafny see that after adding the next value from d to b the prefixes are still the same subsets.
lemma{:verify true} lemmaInvSubsetTakeValueFromD (b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
    requires i <= |c|
    requires j < |d|
    requires i + j < |b|
    requires |c| + |d| == |b|
    requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
    requires b[i+j] == d[j]
    ensures multiset(b[..i+j+1]) == multiset(c[..i])+multiset(d[..j+1])
    {
        assert d[..j]+[d[j]] == d[..j+1];
        assert b[..i+j+1] == b[..i+j] + [b[i+j]];
        assert multiset(b[..i+j+1]) == multiset(c[..i])+multiset(d[..j+1]);
    }