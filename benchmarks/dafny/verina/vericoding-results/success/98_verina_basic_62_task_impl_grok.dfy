// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Find(a: array<int>, key: int) returns (result: int)
    ensures
        (result == -1 || (result >= 0 && result < a.Length)) &&
        (result != -1 ==> (a[result] == key && forall i :: 0 <= i < result ==> a[i] != key)) &&
        (result == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed decreases clause and protected array access in invariant */
    result := -1;
    var i := 0;
    while i < a.Length && result == -1
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] != key
        invariant result == -1 || (0 <= i < a.Length && result == i && a[i] == key)
        invariant result != -1 ==> 0 <= result < a.Length
        decreases a.Length - i, (if result == -1 then 1 else 0)
    {
        if a[i] == key {
            result := i;
        } else {
            i := i + 1;
        }
    }
}
// </vc-code>
