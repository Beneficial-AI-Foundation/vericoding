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
/* helper modified by LLM (iteration 5): fixed for loop syntax for spaces addition */
method ExpandOne(s: string, ts: nat) returns (result: string)
  requires ts > 0
  ensures NoTabs(result)
  ensures (!ContainsTabs(s) ==> result == s)
  ensures |result| >= |s|
  ensures (ContainsTabs(s) ==> |result| > |s|)
  ensures NonTabCharsPreserved(s, result)
{
  ghost var mapping: seq<nat> := [];
  ghost var non_tabs: nat := 0;
  var result_str: string := [];
  var current: nat := 0;
  for j := 0 to |s| - 1
    invariant |mapping| == non_tabs
    invariant NoTabs(result_str)
    invariant forall k: nat :: k < |mapping| ==> mapping[k] < |result_str|
    invariant forall p, q :: 0 <= p < q < |mapping| ==> mapping[p] < mapping[q]
  {
    if s[j] != '	' {
      result_str := result_str + [s[j]];
      mapping := mapping + [current];
      current := current + 1;
      non_tabs := non_tabs + 1;
    } else {
      var tabstop: nat := ((current / ts) + 1) * ts;
      var spaces: nat := tabstop - current;
      for k := 0 to spaces - 1
      {
        result_str := result_str + [' '];
      }
      current := current + spaces;
    }
  }
  result := result_str;
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
  /* code modified by LLM (iteration 5): fixed for loop syntax */
  result := [];
  for i := 0 to |a| - 1
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> NoTabs(result[k])
    invariant forall k :: 0 <= k < i ==> (!ContainsTabs(a[k]) ==> result[k] == a[k])
    invariant forall k :: 0 <= k < i ==> |result[k]| >= |a[k]|
    invariant forall k :: 0 <= k < i ==> (ContainsTabs(a[k]) ==> |result[k]| > |a[k]|)
    invariant forall k :: 0 <= k < i ==> NonTabCharsPreserved(a[k], result[k])
  {
    var expanded := ExpandOne(a[i], tabsize[i]);
    result := result + [expanded];
  }
}
// </vc-code>
