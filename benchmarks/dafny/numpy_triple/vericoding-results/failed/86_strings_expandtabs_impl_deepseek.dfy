// <vc-preamble>
// Predicate to check if a string contains tab characters
predicate ContainsTabs(s: string)
{
    exists i :: 0 <= i < |s| && s[i] == '\t'
}

// Predicate to check if a string contains no tab characters
predicate NoTabs(s: string)
{
    forall i :: 0 <= i < |s| ==> s[i] != '\t'
}

// Predicate to check if non-tab characters are preserved in order
ghost predicate NonTabCharsPreserved(orig: string, result: string)
{
    exists mapping: seq<nat> ::
        |mapping| == |orig| &&
        (forall j :: 0 <= j < |orig| && orig[j] != '\t' ==>
            mapping[j] < |result| && result[mapping[j]] == orig[j]) &&
        (forall j, k :: 0 <= j < k < |orig| && orig[j] != '\t' && orig[k] != '\t' ==>
            mapping[j] < mapping[k])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed while loop with proper boolean condition and termination */
function ComputeExpandedLength(s: string, tabSize: int): (length: int)
  requires tabSize > 0
  ensures length >= |s|
  ensures length > |s| || !ContainsTabs(s)
{
  if |s| == 0 then
    0
  else
    var restLength := ComputeExpandedLength(s[1..], tabSize);
    if s[0] == '\t' then
      restLength + tabSize
    else
      restLength + 1
}

function ExpandString(s: string, tabSize: int): (result: string)
  requires tabSize > 0
  ensures NoTabs(result)
  ensures |result| >= |s|
  ensures |result| > |s| || !ContainsTabs(s)
  ensures !ContainsTabs(s) ==> result == s
  ensures NonTabCharsPreserved(s, result)
{
  if |s| == 0 then
    ""
  else if s[0] == '\t' then
    var spaces := "";
    var i: nat := 0;
    while i < tabSize
      invariant i <= tabSize
      invariant |spaces| == i
      invariant forall j :: 0 <= j < i ==> spaces[j] == ' '
      decreases tabSize - i
    {
      spaces := spaces + " ";
      i := i + 1;
    }
    spaces + ExpandString(s[1..], tabSize)
  else
    s[0..1] + ExpandString(s[1..], tabSize)
}
// </vc-helpers>

// <vc-spec>
method ExpandTabs(a: seq<string>, tabsize: seq<nat>) returns (result: seq<string>)
    requires |a| == |tabsize|
    requires forall i :: 0 <= i < |tabsize| ==> tabsize[i] > 0
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> NoTabs(result[i])
    ensures forall i :: 0 <= i < |a| ==> 
        (!ContainsTabs(a[i]) ==> result[i] == a[i])
    ensures forall i :: 0 <= i < |a| ==> |result[i]| >= |a[i]|
    ensures forall i :: 0 <= i < |a| ==> 
        (ContainsTabs(a[i]) ==> |result[i]| > |a[i]|)
    ensures forall i :: 0 <= i < |a| ==> NonTabCharsPreserved(a[i], result[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed compilation error */
  result := new string[|a|];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == |a|
    invariant forall j :: 0 <= j < i ==> NoTabs(result[j])
    invariant forall j :: 0 <= j < i ==> |result[j]| >= |a[j]|
    invariant forall j :: 0 <= j < i ==> (!ContainsTabs(a[j]) ==> result[j] == a[j])
    invariant forall j :: 0 <= j < i ==> (ContainsTabs(a[j]) ==> |result[j]| > |a[j]|)
    invariant forall j :: 0 <= j < i ==> NonTabCharsPreserved(a[j], result[j])
    decreases |a| - i
  {
    result[i] := ExpandString(a[i], tabsize[i]);
    i := i + 1;
  }
}
// </vc-code>
