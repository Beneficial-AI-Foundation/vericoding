// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RotateRight(l: array<int>, n: nat) returns (result: array<int>)
    ensures
        result.Length == l.Length &&
        (l.Length == 0 || forall i :: 0 <= i < l.Length ==> 
            var len := l.Length;
            var rotatedIndex := ((i - n + len) % len);
            result[i] == l[rotatedIndex])
// </vc-spec>
// <vc-code>
{
  result := new int[l.Length];
  var len := l.Length;
  for i := 0 to len
    invariant 0 <= i <= len
    invariant forall j :: 0 <= j < i ==> result[j] == l[(j - n + len) % len]
  {
    result[i] := l[(i - n + len) % len];
  }
}
// </vc-code>
