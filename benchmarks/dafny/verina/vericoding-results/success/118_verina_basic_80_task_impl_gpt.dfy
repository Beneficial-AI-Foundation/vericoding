// <vc-preamble>
function CountOccurrences(a: seq<int>, key: int): nat
{
    |set i | 0 <= i < |a| && a[i] == key|
}
// </vc-preamble>

// <vc-helpers>
function OnlyOnceSeq(s: seq<int>, key: int): bool { CountOccurrences(s, key) == 1 }
// </vc-helpers>

// <vc-spec>
method OnlyOnce(a: array<int>, key: int) returns (result: bool)
    ensures result <==> CountOccurrences(a[..], key) == 1
// </vc-spec>
// <vc-code>
{
  result := CountOccurrences(a[..], key) == 1;
}
// </vc-code>
