// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function revIndex(len: int, i: int): int
  requires 0 <= i < len
{
  len - 1 - i
}

lemma RevIndexInvolution(len: int, i: int)
  requires 0 <= i < len
  ensures revIndex(len, revIndex(len, i)) == i
{
  calc {
    revIndex(len, revIndex(len, i));
    == { }
    len - 1 - (len - 1 - i);
    == { }
    i;
  }
}
// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>) returns (result: array<int>)
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == a[a.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  result := new int[a.Length];
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> result[j] == a[n - 1 - j]
  {
    result[i] := a[n - 1 - i];
    i := i + 1;
  }
}
// </vc-code>
