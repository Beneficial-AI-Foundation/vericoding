// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function InsertImpl(oline: seq<char>, l: int, nl: seq<char>, p: int, atPos: int): seq<char>
    requires l <= |oline|
    requires p <= |nl|
    requires atPos <= l
    requires l >= 0
    requires p >= 0
    requires atPos >= 0
{
    oline[0..atPos] + nl[0..p] + oline[atPos..l]
}

lemma InsertImplProps(oline: seq<char>, l: int, nl: seq<char>, p: int, atPos: int)
    requires l <= |oline|
    requires p <= |nl|
    requires atPos <= l
    requires l >= 0
    requires p >= 0
    requires atPos >= 0
    ensures |InsertImpl(oline, l, nl, p, atPos)| == l + p
    ensures forall i :: 0 <= i < p ==> InsertImpl(oline, l, nl, p, atPos)[atPos + i] == nl[i]
    ensures forall i :: 0 <= i < atPos ==> InsertImpl(oline, l, nl, p, atPos)[i] == oline[i]
    ensures forall i {:trigger InsertImpl(oline, l, nl, p, atPos)[atPos + p + i]} :: 0 <= i < (l - atPos) ==> InsertImpl(oline, l, nl, p, atPos)[atPos + p + i] == oline[atPos + i]
{
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
  InsertImplProps(oline, l, nl, p, atPos);
  result := InsertImpl(oline, l, nl, p, atPos);
}
// </vc-code>
