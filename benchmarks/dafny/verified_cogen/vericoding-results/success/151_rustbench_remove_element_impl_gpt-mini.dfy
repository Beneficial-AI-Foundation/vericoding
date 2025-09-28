// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function RemoveSeq(a: array<int>, pos: int): seq<int> reads a requires 0 <= pos < a.Length { a[..pos] + a[pos+1..] }
// </vc-helpers>

// <vc-spec>
method RemoveElement(a: array<int>, pos: int) returns (result: seq<int>)
    requires 0 <= pos < a.Length
    ensures |result| == a.Length - 1
    ensures forall i :: 0 <= i < pos ==> result[i] == a[i]
    ensures forall i :: pos <= i < |result| ==> result[i] == a[i + 1]
// </vc-spec>
// <vc-code>
{
  result := RemoveSeq(a, pos);
}
// </vc-code>
