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
/* helper modified by LLM (iteration 5): Replaced the inner loop with a verified recursive function 'Spaces' to simplify the proof of invariants. */
function Spaces(n: nat): (s: string)
    ensures |s| == n
    ensures NoTabs(s)
{
    if n == 0 then "" else " " + Spaces(n - 1)
}

method ExpandTabsInString(s: string, ts: nat) returns (res: string)
    requires ts > 0
    ensures NoTabs(res)
    ensures !ContainsTabs(s) ==> res == s
    ensures |res| >= |s|
    ensures ContainsTabs(s) ==> |res| > |s|
    ensures NonTabCharsPreserved(s, res)
{
    res := "";
    var i: nat := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant NoTabs(res)
        invariant NonTabCharsPreserved(s[..i], res)
        invariant !ContainsTabs(s[..i]) ==> res == s[..i]
        invariant |res| >= i
    {
        if s[i] == '\t' {
            var num_spaces := ts - (|res| % ts);
            res := res + Spaces(num_spaces);
        } else {
            res := res + s[i..i+1];
        }
        i := i + 1;
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
  /* code modified by LLM (iteration 5): No change needed, logic is sound. Errors stemmed from helper implementation complexity. */
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> NoTabs(result[k])
    invariant forall k :: 0 <= k < i ==> (!ContainsTabs(a[k]) ==> result[k] == a[k])
    invariant forall k :: 0 <= k < i ==> |result[k]| >= |a[k]|
    invariant forall k :: 0 <= k < i ==> (ContainsTabs(a[k]) ==> |result[k]| > |a[k]|)
    invariant forall k :: 0 <= k < i ==> NonTabCharsPreserved(a[k], result[k])
  {
      var r := ExpandTabsInString(a[i], tabsize[i]);
      result := result + [r];
      i := i + 1;
  }
}
// </vc-code>
