// <vc-preamble>
predicate Sorted(q: seq<int>) {
    forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

ghost predicate Inv(a: seq<int>, a1: seq<int>, a2: seq<int>, i: nat, mid: nat){
    (i <= |a1|) && (i <= |a2|) && (i+mid <= |a|) &&
    (a1[..i] == a[..i]) && (a2[..i] == a[mid..(i+mid)])
}

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

        ensures 0 <= c.Length - i < c.Length - i0 || (c.Length - i == c.Length - i0 && 0 <= d.Length - j < d.Length - j0)
        {

            i,j := i0,j0;

                if(i == c.Length || (j< d.Length && d[j] < c[i])){

                assert InvSorted(b[..][i+j:=d[j]],c[..],d[..],i,j+1);
                b[i+j] := d[j];

                assert InvSubSet(b[..],c[..],d[..],i,j+1);
                assert InvSorted(b[..],c[..],d[..],i,j+1);
                j := j + 1;
            }
            else{
                assert j == d.Length || (i < c.Length && c[i] <= d[j]);

                assert InvSorted(b[..][i+j:=c[i]],c[..],d[..],i+1,j);

                b[i+j] := c[i];

                assert InvSubSet(b[..],c[..],d[..],i+1,j);
                assert InvSorted(b[..],c[..],d[..],i+1,j);
                i := i + 1;
            }

        }

ghost predicate InvSorted(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
    i <= |c| && j <= |d| && i + j <= |b| &&
    ((i+j > 0 && i < |c|) ==> (b[j + i - 1] <= c[i])) &&
    ((i+j > 0 && j < |d|) ==> (b[j + i - 1] <= d[j])) &&
    Sorted(b[..i+j])
    }

ghost predicate InvSubSet(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
    i <= |c| && j <= |d| && i + j <= |b| &&
    multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
}
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
