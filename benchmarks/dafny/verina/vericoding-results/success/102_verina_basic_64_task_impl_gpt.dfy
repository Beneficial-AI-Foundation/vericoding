// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function InsertSeq(oline: seq<char>, l: int, nl: seq<char>, p: int, atPos: int): seq<char>
  requires 0 <= atPos <= l <= |oline|
  requires 0 <= p <= |nl|
{
  oline[..l][..atPos] + nl[..p] + oline[..l][atPos..]
}
// </vc-helpers>

// <vc-spec>
method Insert(oline: seq<char>, l: int, nl: seq<char>, p: int, atPos: int) returns (result: seq<char>)
    requires l <= |oline|
    requires p <= |nl|
    requires atPos <= l
    requires l >= 0
    requires p >= 0
    requires atPos >= 0
    ensures |result| == l + p
    ensures forall i :: 0 <= i < p ==> result[atPos + i] == nl[i]
    ensures forall i :: 0 <= i < atPos ==> result[i] == oline[i]
    ensures forall i {:trigger result[atPos + p + i]} :: 0 <= i < (l - atPos) ==> result[atPos + p + i] == oline[atPos + i]
// </vc-spec>
// <vc-code>
{
  var orig := oline[..l];
  var ins := nl[..p];
  result := orig[..atPos] + ins + orig[atPos..];
}
// </vc-code>
