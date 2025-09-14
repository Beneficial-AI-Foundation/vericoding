

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    result := [];
    var seen := {};
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result <==> x in seen
        invariant forall x :: x in seen <==> exists j :: 0 <= j < i && a[j] == x
        invariant forall j, k :: 0 <= j < k < |result| ==> result[j] != result[k]
    {
        if a[i] !in seen {
            result := result + [a[i]];
            seen := seen + {a[i]};
        }
        i := i + 1;
    }
}
// </vc-code>

