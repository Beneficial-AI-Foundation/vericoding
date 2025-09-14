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
lemma MultisetSliceProperty<T>(s: seq<T>, i: nat, j: nat)
    requires i <= j <= |s|
    ensures multiset(s[..i]) + multiset(s[i..j]) == multiset(s[..j])
{
    if i == j {
        assert s[..i] == s[..j];
        assert s[i..j] == [];
        assert multiset(s[i..j]) == multiset{};
    } else {
        assert s[..j] == s[..i] + s[i..j];
    }
}

lemma SortedConcatenation(s1: seq<int>, s2: seq<int>, x: int)
    requires Sorted(s1) && Sorted(s2) && |s1| > 0 && |s2| > 0
    requires s1[|s1|-1] <= x <= s2[0]
    ensures Sorted(s1 + [x] + s2)
{
}

lemma MultisetPreservation<T>(a: seq<T>, left: seq<T>, right: seq<T>, mid: nat)
    requires mid <= |a|
    requires left == a[..mid]
    requires right == a[mid..]
    ensures multiset(a[..]) == multiset(left) + multiset(right)
{
    assert a[..] == a[..mid] + a[mid..];
    assert a[..] == left + right;
}

lemma PointwiseToSliceEquality<T>(arr: array<T>, s: seq<T>, n: nat)
    requires n <= arr.Length
    requires n == |s|
    requires forall k :: 0 <= k < n ==> arr[k] == s[k]
    ensures arr[..n] == s
{
}

lemma ArraySliceEquality<T>(arr: array<T>, s: seq<T>)
    requires arr.Length == |s|
    requires forall k :: 0 <= k < arr.Length ==> arr[k] == s[k]
    ensures arr[..] == s
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
        if a.Length == 1 {
            b[0] := a[0];
        }
        return;
    }
    
    var mid := a.Length / 2;
    var left := new int[mid];
    var right := new int[a.Length - mid];
    
    var i := 0;
    while i < mid
        invariant 0 <= i <= mid
        invariant forall k :: 0 <= k < i ==> left[k] == a[k]
    {
        left[i] := a[i];
        i := i + 1;
    }
    
    assert forall k :: 0 <= k < mid ==> left[k] == a[k];
    assert left.Length == mid;
    assert |a[..mid]| == mid;
    ArraySliceEquality(left, a[..mid]);
    
    i := 0;
    while i < a.Length - mid
        invariant 0 <= i <= a.Length - mid
        invariant forall k :: 0 <= k < i ==> right[k] == a[mid + k]
    {
        right[i] := a[mid + i];
        i := i + 1;
    }
    
    assert forall k :: 0 <= k < a.Length - mid ==> right[k] == a[mid + k];
    assert right.Length == a.Length - mid;
    assert |a[mid..]| == a.Length - mid;
    ArraySliceEquality(right, a[mid..]);
    
    assert left[..] == a[..mid];
    assert right[..] == a[mid..];
    MultisetPreservation(a[..], left[..], right[..], mid);
    assert multiset(a[..]) == multiset(left[..]) + multiset(right[..]);
    
    var sortedLeft := MergeSort(left);
    var sortedRight := MergeSort(right);
    
    assert multiset(sortedLeft[..]) == multiset(left[..]);
    assert multiset(sortedRight[..]) == multiset(right[..]);
    assert multiset(a[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
    
    b := new int[a.Length];
    Merge(b, sortedLeft, sortedRight);
    
    assert multiset(b[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
    assert multiset(b[..]) == multiset(a[..]);
}
// </vc-code>

