predicate NoRepeats(words: seq<string>)
{
    forall i, j :: 0 <= i < j < |words| ==> words[i] != words[j]
}

predicate ConsecutiveCharsMatch(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
{
    forall i :: 0 <= i < |words| - 1 ==> words[i][|words[i]| - 1] == words[i+1][0]
}

predicate ValidShiritori(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
{
    NoRepeats(words) && ConsecutiveCharsMatch(words)
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(words: seq<string>) returns (result: string)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> ValidShiritori(words)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var ccm := true;
  var nr := true;
  while i < |words|
    invariant 0 <= i <= |words|
    invariant ccm == (forall j :: 0 <= j < i - 1 ==> words[j][|words[j]| - 1] == words[j+1][0])
    invariant nr == (forall p, q :: 0 <= p < q < i ==> words[p] != words[q])
    decreases |words| - i
  {
    i := i + 1;
    ccm := (forall j :: 0 <= j < i - 1 ==> words[j][|words[j]| - 1] == words[j+1][0]);
    nr := (forall p, q :: 0 <= p < q < i ==> words[p] != words[q]);
  }
  if ccm && nr {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

