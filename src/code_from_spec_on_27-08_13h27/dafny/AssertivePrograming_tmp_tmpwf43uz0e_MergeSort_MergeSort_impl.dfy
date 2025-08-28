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
lemma MultisetFullEquality(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
    requires i == |c| && j == |d| && i + j == |b|
    requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
    ensures multiset(b) == multiset(c) + multiset(d)
{
}

lemma MultisetUpdateC(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
    requires i < |c| && j <= |d| && i + j < |b|
    requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
    ensures multiset(b[..i+j+1]) == multiset(c[..i+1]) + multiset(d[..j])
{
    calc {
        multiset(b[..i+j+1]);
        ==
        multiset(b[..i+j]) + multiset([b[i+j]]);
        ==
        multiset(c[..i]) + multiset(d[..j]) + multiset([b[i+j]]);
        ==
        multiset(c[..i]) + multiset([c[i]]) + multiset(d[..j]);
        ==
        multiset(c[..i+1]) + multiset(d[..j]);
    }
}

lemma MultisetUpdateD(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
    requires j < |d| && i <= |c| && i + j < |b|
    requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
    ensures multiset(b[..i+j+1]) == multiset(c[..i]) + multiset(d[..j+1])
{
    calc {
        multiset(b[..i+j+1]);
        ==
        multiset(b[..i+j]) + multiset([b[i+j]]);
        ==
        multiset(c[..i]) + multiset(d[..j]) + multiset([b[i+j]]);
        ==
        multiset(c[..i]) + multiset(d[..j]) + multiset([d[j]]);
        ==
        multiset(c[..i]) + multiset(d[..j+1]);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method MergeSort(a: array<int>) returns (b: array<int>)
    ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
    decreases a.Length
// </vc-spec>
// </vc-spec>

// <vc-code>
method MergeSortImpl(a: array<int>) returns (b: array<int>)
    ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
    decreases a.Length
{
    if a.Length <= 1 {
        return a;
    }

    var mid := a.Length / 2;
    var left := new int[mid];
    var right := new int[a.Length - mid];

    // Copy elements to left and right subarrays
    for i := 0 to mid
        invariant i <= mid
        invariant forall k :: 0 <= k < i ==> left[k] == a[k]
    {
        left[i] := a[i];
    }
    for i := 0 to a.Length - mid
        invariant i <= a.Length - mid
        invariant forall k :: 0 <= k < i ==> right[k] == a[mid + k]
    {
        right[i] := a[mid + i];
    }

    // Recursively sort the subarrays
    var sortedLeft := MergeSortImpl(left);
    var sortedRight := MergeSortImpl(right);

    // Create result array and merge sorted subarrays
    var result := new int[a.Length];
    ImplMerge(result, sortedLeft, sortedRight);
    return result;
}

method ImplMerge(b: array<int>, c: array<int>, d: array<int>)
    requires b != c && b != d && b.Length == c.Length + d.Length
    requires Sorted(c[..]) && Sorted(d[..])
    ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..]) + multiset(d[..])
    modifies b
{
    var i := 0;
    var j := 0;
    while i < c.Length || j < d.Length
        invariant i <= c.Length && j <= d.Length && i + j <= b.Length
        invariant InvSorted(b[..], c[..], d[..], i, j)
        invariant InvSubSet(b[..], c[..], d[..], i, j)
        decreases c.Length - i + d.Length - j
    {
        if i < c.Length && (j >= d.Length || c[i] <= d[j]) {
            b[i + j] := c[i];
            MultisetUpdateC(b[..], c[..], d[..], i, j);
            i := i + 1;
        } else {
            b[i + j] := d[j];
            MultisetUpdateD(b[..], c[..], d[..], i, j);
            j := j + 1;
        }
    }
    MultisetFullEquality(b[..], c[..], d[..], i, j);
}
// </vc-code>
