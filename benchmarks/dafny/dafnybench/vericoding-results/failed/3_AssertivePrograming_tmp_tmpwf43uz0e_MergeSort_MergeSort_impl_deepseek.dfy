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
lemma LemmaInvSortedBase(b: seq<int>, c: seq<int>, d: seq<int>)
  ensures InvSorted(b, c, d, 0, 0)
{
}

lemma LemmaInvSubSetBase(b: seq<int>, c: seq<int>, d: seq<int>)
  ensures InvSubSet(b, c, d极, 0, 0)
{
}

lemma LemmaChooseFromC(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
  requires InvSorted(b, c, d, i, j) && InvSubSet(b, c, d, i, j)
  requires i < |c| && j < |d| && c[i] <= d[j]
  ensures InvSorted(b, c, d, i+1, j)
  ensures InvSubSet(b, c, d, i+1, j)
{
}

lemma LemmaChooseFromD(b: seq<int>,极 c: seq<int>, d: seq<int>, i: nat, j: nat)
  requires InvSorted(b, c, d, i, j) && InvSubSet(b, c, d, i, j)
  requires i < |c| && j < |d| && d[j] <= c[i]
  ensures InvSorted(b, c, d, i, j+1)
  ensures InvSubSet(b, c, d, i, j+1)
{
}

lemma LemmaFinishFromC(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
  requires InvSorted(b, c, d, i, j) && InvSubSet(b, c, d, i, j)
  requires j >= |d| && i < |c|
  ensures InvSorted(b, c, d, i+1, j)
  ensures InvSubSet(b, c, d, i+1, j)
{
}

lemma LemmaFinishFromD(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
  requires InvSorted(b, c, d, i, j) && Inv极Set(b, c, d, i, j)
  requires i >= |c| && j极 < |d|
  ensures InvSorted(b, c, d, i, j+1)
  ensures InvSubSet(b, c, d, i, j+1)
{
}

lemma LemmaArrayCopyMultiset(a: array<int>, start: int, len: int, b: array<int>)
  requires 0 <= start && start + len <= a.Length
  requires b.Length == len
  requires forall k :: 0 <= k < len ==> b[k] == a[start + k]
  ensures multiset(b[..]) == multiset(a[start..start+len])
{
}

lemma LemmaMergeSortPreservesMultiset(a: array<int>, b: array<int>)
  requires b == MergeSort(a)
  ensures multiset(b[..]) == multiset(a[..])
{
}

lemma LemmaArraySliceMultiset(a: array<int>, start: int, len: int)
  requires 0 <= start && start + len <= a.Length
  ensures multiset(a[start..start+len]) == multiset(a[..])[start..start+len]
{
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
    if a.Length > 0 {
      b[0] := a[0];
    }
    return;
  }
  
  var mid := a.Length / 2;
  
  var left_arr := new int[mid];
  var i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant forall k :: 0 <= k < i ==> left_arr[k] == a[k]
  {
    left_arr[i] := a[i];
    i := i + 1;
  }
  LemmaArrayCopyMultiset(a, 0, mid, left_arr);
  
  var right_arr := new int[a.Length - mid];
  var j := 0;
  while j < a.Length - mid
    invariant 0 <= j <= a.Length - mid
    invariant forall k :: 0 <= k < j ==> right_arr[k] == a[mid + k]
  {
    right_arr[j] := a[mid + j];
    j := j + 1;
  }
  LemmaArrayCopyMultiset(a, mid, a.Length - mid, right_arr);
  
  var sorted_left := MergeSort(left_arr);
  var sorted_right := MergeSort(right_arr);
  
  // Add these assertions to help with verification
  assert multiset(sorted_left[..]) == multiset(left_arr[..]);
  assert multiset(sorted_right[..]) == multiset(right_arr[..]);
  assert multiset(left_arr[..]) == multiset(a[0..mid]);
  assert multiset(right_arr[..]) == multiset(a[mid..a.Length]);
  assert multiset(a[..]) == multiset(a[0..mid]) + multiset(a[mid..a.Length]);
  
  b := new int[a.Length];
  Merge(b, sorted_left, sorted_right);
  
  // Final assertions to complete the proof
  assert multiset(b[..]) == multiset(sorted_left[..]) + multiset(sorted_right[..]);
  assert multiset(b[..]) == multiset(a[..]);
}
// </vc-code>

