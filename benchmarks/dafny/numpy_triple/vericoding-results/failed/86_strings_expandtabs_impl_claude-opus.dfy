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
/* helper modified by LLM (iteration 5): Added explicit mapping witness for NonTabCharsPreserved */
ghost function BuildMapping(s: string, tabsize: nat, offset: nat := 0): seq<nat>
  requires tabsize > 0
  ensures |BuildMapping(s, tabsize, offset)| == |s|
  ensures forall j :: 0 <= j < |s| ==> BuildMapping(s, tabsize, offset)[j] >= offset
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] == '\t' then 
    [offset] + BuildMapping(s[1..], tabsize, offset + tabsize)
  else 
    [offset] + BuildMapping(s[1..], tabsize, offset + 1)
}

function ExpandString(s: string, tabsize: nat): string
  requires tabsize > 0
  ensures NoTabs(ExpandString(s, tabsize))
  ensures |ExpandString(s, tabsize)| >= |s|
  ensures !ContainsTabs(s) ==> ExpandString(s, tabsize) == s
  ensures ContainsTabs(s) ==> |ExpandString(s, tabsize)| > |s|
  ensures NonTabCharsPreserved(s, ExpandString(s, tabsize))
  decreases |s|
{
  if |s| == 0 then
    s
  else if s[0] == '\t' then
    var spaces := seq(tabsize, _ => ' ');
    var rest := ExpandString(s[1..], tabsize);
    var result := spaces + rest;
    ghost var restMapping := BuildMapping(s[1..], tabsize, 0);
    ghost var m := [0] + seq(|s| - 1, i requires 0 <= i < |s| - 1 => tabsize + restMapping[i]);
    assert |m| == |s|;
    assert forall j :: 1 <= j < |s| && s[j] != '\t' ==> 
      m[j] < |result| && result[m[j]] == s[j];
    assert forall j, k :: 0 <= j < k < |s| && s[j] != '\t' && s[k] != '\t' ==> m[j] < m[k];
    assert NonTabCharsPreserved(s, result) by {
      assert exists mapping: seq<nat> :: mapping == m &&
        |mapping| == |s| &&
        (forall j :: 0 <= j < |s| && s[j] != '\t' ==>
            mapping[j] < |result| && result[mapping[j]] == s[j]) &&
        (forall j, k :: 0 <= j < k < |s| && s[j] != '\t' && s[k] != '\t' ==>
            mapping[j] < mapping[k]);
    }
    result
  else
    var rest := ExpandString(s[1..], tabsize);
    var result := [s[0]] + rest;
    ghost var restMapping := BuildMapping(s[1..], tabsize, 0);
    ghost var m := [0] + seq(|s| - 1, i requires 0 <= i < |s| - 1 => 1 + restMapping[i]);
    assert |m| == |s|;
    assert m[0] == 0;
    assert result[0] == s[0];
    assert forall j :: 1 <= j < |s| && s[j] != '\t' ==> 
      m[j] < |result| && result[m[j]] == s[j];
    assert forall j, k :: 0 <= j < k < |s| && s[j] != '\t' && s[k] != '\t' ==> m[j] < m[k];
    assert NonTabCharsPreserved(s, result) by {
      assert exists mapping: seq<nat> :: mapping == m &&
        |mapping| == |s| &&
        (forall j :: 0 <= j < |s| && s[j] != '\t' ==>
            mapping[j] < |result| && result[mapping[j]] == s[j]) &&
        (forall j, k :: 0 <= j < k < |s| && s[j] != '\t' && s[k] != '\t' ==>
            mapping[j] < mapping[k]);
    }
    result
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
/* code modified by LLM (iteration 5): Using ExpandString helper function */
{
  var i := 0;
  result := [];
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> NoTabs(result[j])
    invariant forall j :: 0 <= j < i ==> (!ContainsTabs(a[j]) ==> result[j] == a[j])
    invariant forall j :: 0 <= j < i ==> |result[j]| >= |a[j]|
    invariant forall j :: 0 <= j < i ==> (ContainsTabs(a[j]) ==> |result[j]| > |a[j]|)
    invariant forall j :: 0 <= j < i ==> NonTabCharsPreserved(a[j], result[j])
  {
    var expanded := ExpandString(a[i], tabsize[i]);
    result := result + [expanded];
    i := i + 1;
  }
}
// </vc-code>
