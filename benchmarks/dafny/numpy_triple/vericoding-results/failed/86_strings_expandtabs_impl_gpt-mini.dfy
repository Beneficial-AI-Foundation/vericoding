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
/* helper modified by LLM (iteration 5): use substring s[i..i+1] instead of ToString to convert char to string */
method ExpandLine(s: string, tabsize: nat) returns (res: string)
  requires tabsize > 0
  ensures NoTabs(res)
  ensures |res| >= |s|
  ensures (!ContainsTabs(s) ==> res == s)
  ensures (ContainsTabs(s) ==> |res| > |s|)
  ensures NonTabCharsPreserved(s, res)
{
  var sb := "";
  var i := 0;
  var mapping: seq<nat> := [];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |mapping| == i
    invariant forall j :: 0 <= j < i && s[j] != '\t' ==> mapping[j] < |sb| && sb[mapping[j]] == s[j]
    invariant forall j, k :: 0 <= j < k < i && s[j] != '\t' && s[k] != '\t' ==> mapping[j] < mapping[k]
  {
    if s[i] != '\t' {
      var idx := |sb|;
      mapping := mapping + [idx];
      sb := sb + s[i..i+1];
    } else {
      var col := |sb|;
      var spaces := tabsize - (col % tabsize);
      var k := 0;
      while k < spaces
        invariant 0 <= k <= spaces
        invariant |sb| == col + k
      {
        sb := sb + " ";
        k := k + 1;
      }
      mapping := mapping + [0];
    }
    i := i + 1;
  }
  res := sb;
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
/* code modified by LLM (iteration 5): implemented ExpandTabs using ExpandLine */
{
  var i := 0;
  result := [];
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> NoTabs(result[k]) && |result[k]| >= |a[k]| && (!ContainsTabs(a[k]) ==> result[k] == a[k]) && (ContainsTabs(a[k]) ==> |result[k]| > |a[k]|) && NonTabCharsPreserved(a[k], result[k])
  {
    var r := ExpandLine(a[i], tabsize[i]);
    result := result + [r];
    i := i + 1;
  }
}

// </vc-code>
