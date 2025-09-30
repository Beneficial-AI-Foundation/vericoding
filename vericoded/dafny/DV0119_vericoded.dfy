// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Abs(x: int): int { if x >= 0 then x else -x }
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
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant forall k :: 0 <= k < i ==> result[k] == l[((k - n + len) % len)]
    decreases len - i
  {
    result[i] := l[((i - n + len) % len)];
    i := i + 1;
  }
}

// </vc-code>
