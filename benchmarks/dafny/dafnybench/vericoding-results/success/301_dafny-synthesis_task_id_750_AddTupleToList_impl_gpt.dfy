

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AddTupleToList(l: seq<(int, int)>, t: (int, int)) returns (r: seq<(int, int)>)
    ensures |r| == |l| + 1
    ensures r[|r| - 1] == t
    ensures forall i :: 0 <= i < |l| ==> r[i] == l[i]
// </vc-spec>
// <vc-code>
{
  r := l + [t];
}
// </vc-code>

