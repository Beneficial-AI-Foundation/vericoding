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

//This is a method that replace the loop body
method MergeLoop(b: array<int>, c: array<int>, d: array<int>,i0: nat , j0: nat)  returns (i: nat, j: nat)
        requires b != c && b != d && b.Length == c.Length + d.Length
        requires Sorted(c[..]) && Sorted(d[..])
        requires i0 <= c.Length && j0 <= d.Length && i0 + j0 <= b.Length
        requires InvSubSet(b[..],c[..],d[..],i0,j0)
        requires InvSorted(b[..],c[..],d[..],i0,j0)
        requires i0 + j0 < b.Length

        modifies b

        ensures i <= c.Length && j <= d.Length && i + j <= b.Length
        ensures InvSubSet(b[..],c[..],d[..],i,j)
        ensures InvSorted(b[..],c[..],d[..],i,j)
        //decreases ensures
        ensures 0 <= c.Length - i < c.Length - i0 || (c.Length - i == c.Length - i0 && 0 <= d.Length - j < d.Length - j0)
        {

            i,j := i0,j0;

                if(i == c.Length || (j< d.Length && d[j] < c[i])){
                    // in this case we take the next value from d
                assert InvSorted(b[..][i+j:=d[j]],c[..],d[..],i,j+1);
                b[i+j] := d[j];

                assert InvSubSet(b[..],c[..],d[..],i,j+1);
                assert InvSorted(b[..],c[..],d[..],i,j+1);
                j := j + 1;
            }
            else{
                assert j == d.Length || (i < c.Length && c[i] <= d[j]);
                    // in this case we take the next value from c
                assert InvSorted(b[..][i+j:=c[i]],c[..],d[..],i+1,j);

                b[i+j] := c[i];

                assert InvSubSet(b[..],c[..],d[..],i+1,j);
                assert InvSorted(b[..],c[..],d[..],i+1,j);
                i := i + 1;
            }


        }


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
lemma LemmaMultisetPrefix(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat)
    requires i == |c| && j == |d| && i + j == |b|
    requires multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
    ensures multiset(b) == multiset(c) + multiset(d)
{
    assert b[..i+j] == b[..];
    assert c[..i] == c[..];
    assert d[..j] == d[..];
}

lemma LemmaSortedPrefix(b: seq<int>, i: nat, j: nat)
    requires i + j == |b|
    requires Sorted(b[..i+j])
    ensures Sorted(b)
{
    assert b[..i+j] == b[..];
}
// </vc-helpers>

// <vc-spec>
method Merge(b: array<int>, c: array<int>, d: array<int>)
    requires b != c && b != d && b.Length == c.Length + d.Length
    requires Sorted(c[..]) && Sorted(d[..])
    ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
    modifies b
// </vc-spec>
// <vc-code>
{
    var i: nat := 0;
    var j: nat := 0;
    
    while i + j < b.Length
        invariant i <= c.Length && j <= d.Length && i + j <= b.Length
        invariant InvSubSet(b[..], c[..], d[..], i, j)
        invariant InvSorted(b[..], c[..], d[..], i, j)
        decreases c.Length - i, d.Length - j
    {
        i, j := MergeLoop(b, c, d, i, j);
    }
    
    assert i == c.Length && j == d.Length && i + j == b.Length;
    
    LemmaMultisetPrefix(b[..], c[..], d[..], i, j);
    LemmaSortedPrefix(b[..], i, j);
}
// </vc-code>

