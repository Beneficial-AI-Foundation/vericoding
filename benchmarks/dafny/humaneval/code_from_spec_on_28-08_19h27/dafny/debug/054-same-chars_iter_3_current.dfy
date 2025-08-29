// <vc-helpers>
function CountChar(s: string, c: char): nat
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function GetAllChars(s: string): set<char>
{
  if |s| == 0 then {}
  else {s[0]} + GetAllChars(s[1..])
}

lemma SetToSeqLemma(s: set<char>, charSeq: seq<char>)
  requires forall c :: c in s <==> c in charSeq
  ensures s == set c | c in charSeq
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def same_chars(s0: string, s1: string) -> Bool
*/
// </vc-description>

// <vc-spec>
method same_chars(s0: string, s1: string) returns (result: bool)
  ensures result <==> (forall c :: c in GetAllChars(s0) + GetAllChars(s1) ==> CountChar(s0, c) == CountChar(s1, c))
// </vc-spec>
// <vc-code>
{
  var chars0 := GetAllChars(s0);
  var chars1 := GetAllChars(s1);
  var allChars := chars0 + chars1;
  
  var charSeq := [];
  var tempChars := allChars;
  
  while tempChars != {}
    decreases |tempChars|
    invariant forall c :: c in allChars - tempChars <==> c in charSeq
  {
    var c :| c in tempChars;
    charSeq := charSeq + [c];
    tempChars := tempChars - {c};
  }
  
  assert forall c :: c in allChars <==> c in charSeq;
  
  var i := 0;
  result := true;
  
  while i < |charSeq| && result
    invariant 0 <= i <= |charSeq|
    invariant forall c :: c in allChars <==> c in charSeq
    invariant result ==> forall j :: 0 <= j < i ==> CountChar(s0, charSeq[j]) == CountChar(s1, charSeq[j])
    invariant !result ==> exists j :: 0 <= j < i && CountChar(s0, charSeq[j]) != CountChar(s1, charSeq[j])
  {
    var c := charSeq[i];
    var count0 := CountChar(s0, c);
    var count1 := CountChar(s1, c);
    
    if count0 != count1 {
      result := false;
    }
    i := i + 1;
  }
  
  if result {
    assert forall j :: 0 <= j < |charSeq| ==> CountChar(s0, charSeq[j]) == CountChar(s1, charSeq[j]);
    assert forall c :: c in charSeq ==> CountChar(s0, c) == CountChar(s1, c);
    assert forall c :: c in allChars ==> CountChar(s0, c) == CountChar(s1, c);
  }
}
// </vc-code>
