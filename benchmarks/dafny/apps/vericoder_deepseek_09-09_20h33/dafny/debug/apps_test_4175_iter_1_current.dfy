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
lemma NoRepeatsImpliesNoRepeatsUpTo(words: seq<string>, n: int)
  requires 0 <= n <= |words|
  requires forall i, j :: 0 <= i < j < |words| ==> words[i] != words[j]
  ensures forall i, j :: 0 <= i < j < n ==> words[i] != words[j]
{
}

lemma ConsecutiveCharsMatchImpliesToIndex(words: seq<string>, n: int)
  requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
  requires forall i :: 0 <= i < |words| - 1 ==> words[i][|words[i]| - 1] == words[i+1][0]
  requires 0 <= n <= |words| - 1
  ensures forall i :: 0 <= i < n ==> words[i][|words[i]| - 1] == words[i+1][0]
{
}
// </vc-helpers>

// <vc-spec>
method solve(words: seq<string>) returns (result: string)
    requires forall i :: 0 <= i < |words| ==> |words[i]| > 0
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> ValidShiritori(words)
// </vc-spec>
// <vc-code>
{
  if |words| == 0 {
    result := "Yes";
    return;
  }
  
  var i := 0;
  var seen: set<string> := {};
  
  while i < |words|
    invariant 0 <= i <= |words|
    invariant forall w :: w in seen ==> w in words[0..i]
    invariant forall j, k :: 0 <= j < k < i ==> words[j] != words[k]
    invariant i > 0 ==> forall j :: 0 <= j < i-1 ==> words[j][|words[j]| - 1] == words[j+1][0]
  {
    var current := words[i];
    
    if current in seen {
      result := "No";
      return;
    }
    seen := seen + {current};
    
    if i > 0 {
      var prev := words[i-1];
      if prev[|prev| - 1] != current[0] {
        result := "No";
        return;
      }
    }
    
    i := i + 1;
  }
  
  result := "Yes";
}
// </vc-code>

