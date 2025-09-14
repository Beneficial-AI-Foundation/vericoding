// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function EvensSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [] else
    if s[0] % 2 == 0 then [s[0]] + EvensSeq(s[1..]) else EvensSeq(s[1..])
}

lemma EvensSeqProperties(s: seq<int>)
  ensures |EvensSeq(s)| <= |s|
  ensures forall i :: 0 <= i < |EvensSeq(s)| ==> EvensSeq(s)[i] % 2 == 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    var x := s[0];
    EvensSeqProperties(s[1..]);
    if x % 2 == 0 {
      assert |EvensSeq(s)| == 1 + |EvensSeq(s[1..])|;
      assert |EvensSeq(s)| <= 1 + |s[1..]|;
      assert 1 + |s[1..]| == |s|;
      assert EvensSeq(s)[0] % 2 == 0;
      assert forall j :: 0 <= j < |EvensSeq(s[1..])| ==> EvensSeq(s[1..])[j] % 2 == 0;
      assert forall i :: 1 <= i < |EvensSeq(s)| ==> EvensSeq(s)[i] % 2 == 0;
    } else {
      assert |EvensSeq(s)| == |EvensSeq(s[1..])|;
      assert forall i :: 0 <= i < |EvensSeq(s)| ==> EvensSeq(s)[i] % 2 == 0;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method RemoveOdds(arr: array<int>) returns (even_list: seq<int>)
    ensures |even_list| <= arr.Length
    ensures forall i :: 0 <= i < |even_list| ==> even_list[i] % 2 == 0
// </vc-spec>
// <vc-code>
{
  var s := arr[..];
  even_list := EvensSeq(s);
  EvensSeqProperties(s);
}

// </vc-code>
