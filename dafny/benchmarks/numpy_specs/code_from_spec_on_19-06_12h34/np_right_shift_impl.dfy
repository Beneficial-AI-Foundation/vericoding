Let me add an assertion after the loop to help Dafny verify that the loop invariant implies the postcondition:

//IMPL
method RightShift(a: array<int>, b: array<nat>) returns (res: array<int>)
requires a.Length == b.Length
requires forall i :: 0 <= i < b.Length ==> b[i] < 64
ensures res.Length == a.Length
ensures forall i :: 0 <= i < a.Length ==> res[i] == a[i] >> b[i]
{
    res := new int[a.Length];
    for i := 0 to a.Length
        invariant forall j :: 0 <= j < i ==> res[j] == a[j] >> b[j]
    {
        res[i] := a[i] >> b[i];
    }
    /* code modified by LLM (iteration 2): added assertion to help Dafny prove postcondition from loop invariant */
    assert forall j :: 0 <= j < a.Length ==> res[j] == a[j] >> b[j];
}