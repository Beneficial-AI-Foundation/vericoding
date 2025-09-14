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
lemma MergeHelper(b: array<int>, c: array<int>, d: array<int>, i: int, j: int)
    requires b.Length == c.Length + d.Length
    requires 0 <= i <= c.Length && 0 <= j <= d.Length
    requires InvSorted(b[..], c[..], d[..], i, j)
    requires InvSubSet(b[..], c[..], d[..], i, j)
    requires i < c.Length && j < d.Length && c[i] <= d[j]
    ensures InvSorted(b[..], c[..], d[..], i+1, j)
    ensures InvSubSet(b[..], c[..], d[..], i+1, j)
{
    var oldB := b[..];
    var newB := oldB[i+j := c[i]];
    var newI := i + 1;
    
    assert newI <= c.Length;
    assert j <= d.Length;
    assert newI + j == (i+1) + j == i+j+1 <= b.Length;
    
    if i+j > 0 {
        if i < c.Length {
            assert b[i+j-1] <= c[i];
            assert newB[newI+j-1] == newB[i+j] == c[i];
            assert c[newI] == c[i+1];
            assert newB[newI+j-1] == c[i] <= c[i] <= c[i+1] == c[newI];
        }
        if j < d.Length {
            assert b[i+j-1] <= d[j];
            assert newB[newI+j-1] == c[i] <= d[j];
        }
    }
    
    if newI+j > 0 {
        if newI+j == 1 {
            assert newB[..1] == [c[i]];
            assert Sorted([c[i]]);
        } else {
            assert newB[..newI+j] == newB[..i+j] + [c[i]];
            assert Sorted(newB[..i+j]);
            assert |newB[..i+j]| == i+j > 0;
            assert newB[i+j-1] == b[i+j-1];
            assert b[i+j-1] <= c[i];
            assert newB[i+j-1] <= c[i];
        }
    }
    
    assert multiset(newB[..newI+j]) == multiset(newB[..i+j]) + multiset([c[i]]);
    assert multiset(newB[..i+j]) == multiset(oldB[..i+j]);
    assert multiset(oldB[..i+j]) == multiset(c[..i]) + multiset(d[..j]);
    assert multiset(newB[..newI+j]) == multiset(c[..i]) + multiset(d[..j]) + multiset([c[i]]);
    assert multiset(c[..newI]) == multiset(c[..i+1]) == multiset(c[..i]) + multiset([c[i]]);
    assert multiset(newB[..newI+j]) == multiset(c[..newI]) + multiset(d[..j]);
}

lemma MergeHelper2(b: array<int>, c: array<int>, d: array<int>, i: int, j: int)
    requires b.Length == c.Length + d.Length
    requires 0 <= i <= c.Length && 0 <= j <= d.Length
    requires InvSorted(b[..], c[..], d[..], i, j)
    requires InvSubSet(b[..], c[..], d[..], i, j)
    requires i < c.Length && j < d.Length && d[j] < c[i]
    ensures InvSorted(b[..], c[..], d[..], i, j+1)
    ensures InvSubSet(b[..], c[..], d[..], i, j+1)
{
    var oldB := b[..];
    var newB := oldB[i+j := d[j]];
    var newJ := j + 1;
    
    assert i <= c.Length;
    assert newJ <= d.Length;
    assert i + newJ == i + j + 1 <= b.Length;
    
    if i+j > 0 {
        if i < c.Length {
            assert b[i+j-1] <= c[i];
            assert newB[i+newJ-1] == d[j] < c[i];
        }
        if j < d.Length {
            assert b[i+j-1] <= d[j];
            assert newB[i+newJ-1] == d[j];
            assert d[newJ] == d[j+1];
            assert newB[i+newJ-1] == d[j] <= d[j] <= d[j+1] == d[newJ];
        }
    }
    
    if i+newJ > 0 {
        if i+newJ == 1 {
            assert newB[..1] == [d[j]];
            assert Sorted([d[j]]);
        } else {
            assert newB[..i+newJ] == newB[..i+j] + [d[j]];
            assert Sorted(newB[..i+j]);
            assert newB[i+j-1] == b[i+j-1] <= d[j];
        }
    }
    
    assert multiset(newB[..i+newJ]) == multiset(newB[..i+j]) + multiset([d[j]]);
    assert multiset(newB[..i+j]) == multiset(oldB[..i+j]);
    assert multiset(oldB[..i+j]) == multiset(c[..i]) + multiset(d[..j]);
    assert multiset(newB[..i+newJ]) == multiset(c[..i]) + multiset(d[..j]) + multiset([d[j]]);
    assert multiset(d[..newJ]) == multiset(d[..j+1]) == multiset(d[..j]) + multiset([d[j]]);
    assert multiset(newB[..i+newJ]) == multiset(c[..i]) + multiset(d[..newJ]);
}

method {:verified} Merge(b: array<int>, c: array<int>, d: array<int>)
    requires b != c && b != d && b.Length == c.Length + d.Length
    requires Sorted(c[..]) && Sorted(d[..])
    ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
    modifies b
{
    var i := 0;
    var j := 0;
    
    while i < c.Length || j < d.Length
        invariant InvSorted(b[..], c[..], d[..], i, j)
        invariant InvSubSet(b[..], c[..], d[..], i, j)
    {
        if i < c.Length && (j >= d.Length || c[i] <= d[j]) {
            b[i+j] := c[i];
            MergeHelper(b, c, d, i, j);
            i := i + 1;
        } else {
            b[i+j] := d[j];
            MergeHelper2(b, c, d, i, j);
            j := j + 1;
        }
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
        if a.Length == 1 {
            b[0] := a[0];
        }
    } else {
        var mid := a.Length / 2;
        var leftArr := a[..mid].ToArray();
        var rightArr := a[mid..].ToArray();
        var sortedLeft := MergeSort(leftArr);
        var sortedRight := MergeSort(rightArr);
        b := new int[a.Length];
        Merge(sortedLeft, sortedRight, b);
    }
}
// </vc-code>

