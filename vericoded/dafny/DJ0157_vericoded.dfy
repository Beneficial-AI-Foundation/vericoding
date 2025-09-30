// <vc-preamble>
predicate InArray(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added helper predicate for uniqueness checking */
predicate IsUnique(s: seq<int>, i: int)
{
    0 <= i < |s| && forall j :: 0 <= j < |s| && j != i ==> s[i] != s[j]
}

predicate NotInB(a: seq<int>, b: seq<int>, i: int)
{
    0 <= i < |a| && !InArray(b, a[i])
}
// </vc-helpers>

// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (c: array<int>)
    ensures forall k :: 0 <= k < c.Length ==> InArray(a[..], c[k]) && !InArray(b[..], c[k])
    ensures forall i, j :: 0 <= i < j < c.Length ==> c[i] != c[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed postcondition verification by ensuring proper invariants */
{
    var temp := new int[a.Length];
    var count := 0;
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= count <= i
        invariant forall k :: 0 <= k < count ==> InArray(a[..], temp[k]) && !InArray(b[..], temp[k])
        invariant forall j, k :: 0 <= j < k < count ==> temp[j] != temp[k]
        invariant forall k :: 0 <= k < count ==> exists m :: 0 <= m < i && temp[k] == a[m]
    {
        var isInB := false;
        var j := 0;
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant isInB <==> exists k :: 0 <= k < j && b[k] == a[i]
        {
            if b[j] == a[i] {
                isInB := true;
            }
            j := j + 1;
        }
        
        if !isInB {
            var isDuplicate := false;
            var k := 0;
            while k < count
                invariant 0 <= k <= count
                invariant isDuplicate <==> exists m :: 0 <= m < k && temp[m] == a[i]
            {
                if temp[k] == a[i] {
                    isDuplicate := true;
                }
                k := k + 1;
            }
            
            if !isDuplicate {
                temp[count] := a[i];
                count := count + 1;
            }
        }
        i := i + 1;
    }
    
    c := new int[count];
    i := 0;
    while i < count
        invariant 0 <= i <= count
        invariant forall k :: 0 <= k < i ==> c[k] == temp[k]
        invariant forall k :: 0 <= k < count ==> InArray(a[..], temp[k]) && !InArray(b[..], temp[k])
        invariant forall j, k :: 0 <= j < k < count ==> temp[j] != temp[k]
    {
        c[i] := temp[i];
        i := i + 1;
    }
    
    assert forall k :: 0 <= k < c.Length ==> c[k] == temp[k];
    assert forall k :: 0 <= k < c.Length ==> InArray(a[..], c[k]) && !InArray(b[..], c[k]);
    assert forall j, k :: 0 <= j < k < c.Length ==> c[j] != c[k];
}
// </vc-code>
