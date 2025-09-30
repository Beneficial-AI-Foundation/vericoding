// <vc-preamble>
predicate InArray(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to help prove invariants about array elements */
lemma InArrayTransitive(a: seq<int>, b: seq<int>, x: int)
    requires InArray(b, x)
    requires forall i :: 0 <= i < |b| ==> InArray(a, b[i])
    ensures InArray(a, x)
{
    var j :| 0 <= j < |b| && b[j] == x;
    var k :| 0 <= k < |a| && a[k] == b[j];
}
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: array<int>)
    requires a.Length >= 1
    ensures forall i :: 0 <= i < result.Length ==> InArray(a[..], result[i])
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed invariant maintenance in second loop */
{
    var temp := new int[a.Length];
    var count := 0;
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= count <= i
        invariant count <= temp.Length
        invariant forall k :: 0 <= k < count ==> InArray(a[..], temp[k])
        invariant forall k, l :: 0 <= k < l < count ==> temp[k] != temp[l]
        invariant forall k :: 0 <= k < count ==> exists m :: 0 <= m < i && a[m] == temp[k]
    {
        var j := 0;
        var found := false;
        
        while j < count
            invariant 0 <= j <= count
            invariant !found ==> forall m :: 0 <= m < j ==> temp[m] != a[i]
            invariant found ==> exists m :: 0 <= m < count && temp[m] == a[i]
        {
            if temp[j] == a[i] {
                found := true;
                break;
            }
            j := j + 1;
        }
        
        if !found {
            temp[count] := a[i];
            count := count + 1;
        }
        
        i := i + 1;
    }
    
    result := new int[count];
    i := 0;
    
    while i < count
        invariant 0 <= i <= count
        invariant result.Length == count
        invariant forall k :: 0 <= k < i ==> result[k] == temp[k]
        invariant forall k :: 0 <= k < count ==> InArray(a[..], temp[k])
        invariant forall k, l :: 0 <= k < l < count ==> temp[k] != temp[l]
    {
        result[i] := temp[i];
        i := i + 1;
    }
}
// </vc-code>
