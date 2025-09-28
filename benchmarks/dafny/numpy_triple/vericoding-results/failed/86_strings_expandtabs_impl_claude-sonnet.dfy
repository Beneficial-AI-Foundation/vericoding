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
// Helper function to expand tabs in a single string
function ExpandTabsInString(s: string, tabSize: nat): string
    requires tabSize > 0
    ensures NoTabs(ExpandTabsInString(s, tabSize))
    ensures |ExpandTabsInString(s, tabSize)| >= |s|
    ensures !ContainsTabs(s) ==> ExpandTabsInString(s, tabSize) == s
    decreases |s|
{
    if |s| == 0 then ""
    else if s[0] == '\t' then
        var spaces := seq(tabSize, _ => ' ');
        spaces + ExpandTabsInString(s[1..], tabSize)
    else
        [s[0]] + ExpandTabsInString(s[1..], tabSize)
}

/* helper modified by LLM (iteration 5): Simplified postconditions to focus on essential properties */
lemma NonTabCharsPreservedLemma(s: string, tabSize: nat)
    requires tabSize > 0
    ensures NonTabCharsPreserved(s, ExpandTabsInString(s, tabSize))
    decreases |s|
{
    var result := ExpandTabsInString(s, tabSize);
    
    if |s| == 0 {
        var mapping: seq<nat> := [];
        assert NonTabCharsPreserved(s, result);
    } else if s[0] == '\t' {
        NonTabCharsPreservedLemma(s[1..], tabSize);
        var spaces := seq(tabSize, _ => ' ');
        var tail_result := ExpandTabsInString(s[1..], tabSize);
        
        var tail_mapping: seq<nat> :| 
            |tail_mapping| == |s[1..]| &&
            (forall j :: 0 <= j < |s[1..]| && s[1..][j] != '\t' ==>
                tail_mapping[j] < |tail_result| && tail_result[tail_mapping[j]] == s[1..][j]) &&
            (forall j, k :: 0 <= j < k < |s[1..]| && s[1..][j] != '\t' && s[1..][k] != '\t' ==>
                tail_mapping[j] < tail_mapping[k]);
        
        var mapping := [0] + seq(|s[1..]|, i requires 0 <= i < |s[1..]| => 
            if i < |tail_mapping| then tail_mapping[i] + tabSize else 0);
        
        assert NonTabCharsPreserved(s, result);
    } else {
        NonTabCharsPreservedLemma(s[1..], tabSize);
        var tail_result := ExpandTabsInString(s[1..], tabSize);
        
        var tail_mapping: seq<nat> :|
            |tail_mapping| == |s[1..]| &&
            (forall j :: 0 <= j < |s[1..]| && s[1..][j] != '\t' ==>
                tail_mapping[j] < |tail_result| && tail_result[tail_mapping[j]] == s[1..][j]) &&
            (forall j, k :: 0 <= j < k < |s[1..]| && s[1..][j] != '\t' && s[1..][k] != '\t' ==>
                tail_mapping[j] < tail_mapping[k]);
        
        var mapping := [0] + seq(|s[1..]|, i requires 0 <= i < |s[1..]| => 
            if i < |tail_mapping| then tail_mapping[i] + 1 else 0);
        
        assert NonTabCharsPreserved(s, result);
    }
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
  /* code modified by LLM (iteration 5): Simplified implementation calling helper lemma */
  var temp: seq<string> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |temp| == i
    invariant forall j :: 0 <= j < i ==> NoTabs(temp[j])
    invariant forall j :: 0 <= j < i ==> (!ContainsTabs(a[j]) ==> temp[j] == a[j])
    invariant forall j :: 0 <= j < i ==> |temp[j]| >= |a[j]|
    invariant forall j :: 0 <= j < i ==> (ContainsTabs(a[j]) ==> |temp[j]| > |a[j]|)
    invariant forall j :: 0 <= j < i ==> NonTabCharsPreserved(a[j], temp[j])
  {
    var expanded := ExpandTabsInString(a[i], tabsize[i]);
    NonTabCharsPreservedLemma(a[i], tabsize[i]);
    temp := temp + [expanded];
    i := i + 1;
  }
  result := temp;
}
// </vc-code>
