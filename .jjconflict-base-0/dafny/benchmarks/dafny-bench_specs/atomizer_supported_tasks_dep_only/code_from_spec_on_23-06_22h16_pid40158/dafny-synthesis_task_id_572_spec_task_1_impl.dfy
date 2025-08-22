//IMPL 
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    result := [];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result <==> exists k :: 0 <= k < i && a[k] == x
        invariant forall p, q :: 0 <= p < q < |result| ==> result[p] != result[q]
    {
        if a[i] !in result {
            result := result + [a[i]];
        }
        i := i + 1;
    }
}