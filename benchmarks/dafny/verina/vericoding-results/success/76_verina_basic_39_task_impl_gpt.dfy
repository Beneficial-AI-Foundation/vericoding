// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function RotIdx(i: int, n: nat, len: int): int
  requires len > 0
  ensures 0 <= RotIdx(i, n, len) < len
{
  ((i - n + len) % len)
}
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
  if l.Length > 0 {
    var len := l.Length;
    var i := 0;
    while i < len
      invariant 0 <= i <= len
      invariant result.Length == len
      invariant forall j :: 0 <= j < i ==> result[j] == l[RotIdx(j, n, len)]
      decreases len - i
    {
      var idx := RotIdx(i, n, len);
      result[i] := l[idx];
      i := i + 1;
    }
  }
}
// </vc-code>
