// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function rotIndex(i: int, n: nat, len: nat): int
  requires len > 0
  ensures 0 <= rotIndex(i, n, len) < len
{ (i - n + len) % len }
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
  if len == 0 {
    return;
  }
  var k := 0;
  while k < len
    invariant 0 <= k <= len
    invariant len > 0
    invariant forall i :: 0 <= i < k ==> result[i] == l[(i - n + len) % len]
    decreases len - k
  {
    result[k] := l[(k - n + len) % len];
    k := k + 1;
  }
}
// </vc-code>
