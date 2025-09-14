// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    requires 
        a.Length > 0 &&
        b.Length > 0
    ensures
        result == (exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j])
// </vc-spec>
// <vc-code>
{
    result := false;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant !result ==> (forall ii :: 0 <= ii < i ==> (forall jj :: 0 <= jj < b.Length ==> a[ii] != b[jj]))
        decreases a.Length - i
    {
        var j := 0;
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant (forall jj :: 0 <= jj < j ==> a[i] != b[jj])
            decreases b.Length - j
        {
            if a[i] == b[j] {
                result := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}
// </vc-code>
