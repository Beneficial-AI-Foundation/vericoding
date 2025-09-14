

// <vc-helpers>
lemma {:induction false} multiply_div(n: int)
  requires n % 2 == 0
  ensures 2 * (n / 2) == n
{}
// </vc-helpers>

// <vc-spec>
method PairwiseAddition(a: array<int>) returns (result: array<int>)
    requires a != null
    requires a.Length % 2 == 0
    ensures result != null
    ensures result.Length == a.Length / 2
    ensures forall i :: 0 <= i < result.Length ==> result[i] == a[2*i] + a[2*i + 1]
// </vc-spec>
// <vc-code>
{
    var n := a.Length;
    var result_len := n / 2;
    result := new int[result_len];
    multiply_div(n); // Prove array indexing is safe.

    var i := 0;
    while i < result_len
        invariant 0 <= i <= result_len
        invariant forall j :: 0 <= j < i ==> result[j] == a[2*j] + a[2*j + 1]
        invariant a.Length == n
        invariant result.Length == result_len
        invariant 2*i <= a.Length
        invariant 2*i + 1 <= a.Length
    {
        result[i] := a[2*i] + a[2*i + 1];
        i := i + 1;
    }
    return result;
}
// </vc-code>

