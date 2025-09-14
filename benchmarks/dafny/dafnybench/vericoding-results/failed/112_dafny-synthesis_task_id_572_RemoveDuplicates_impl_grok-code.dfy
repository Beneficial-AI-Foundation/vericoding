

// <vc-helpers>
// Helper for tracking seen elements
method RemoveDuplicatesHelper(a: array?<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    var seen: set<int> := {};
    var i: nat := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in seen <==> exists k :: 0 <= k < i && a[k] == x
        invariant forall x :: x in res <==> x in seen
        invariant forall m, n :: 0 <= m < n < |res| ==> res[m] != res[n]
    {
        if a[i] !in seen {
            seen := seen + {a[i]};
            res := res + [a[i]];
        }
        i := i + 1;
    }
    result := res;
}
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var seen: set<int> := {};
  var i: nat := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in seen <==> exists k :: 0 <= k < i && a[k] == x
    invariant forall x :: x in res <==> x in seen
    invariant forall m, n :: 0 <= m < n < |res| ==> res[m] != res[n]
  {
    if a[i] !in seen {
      seen := seen + {a[i]};
      res := res + [a[i]];
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>

