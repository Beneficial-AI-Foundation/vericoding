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
/* helper modified by LLM (iteration 5): Corrected array initialization for functions. */
function ExpandStringTabs(s: string, tabsize: nat): string
{
    var result := new char[(|s| * tabsize)];
    var resultIdx := 0;

    for i := 0 to |s| - 1
        invariant 0 <= i <= |s|
        invariant 0 <= resultIdx <= |s| * tabsize
        invariant forall k :: 0 <= k < resultIdx ==> result[k] != '\t' // Characters filled so far contain no tabs
        invariant result.Length == |s| * tabsize
    {
        if s[i] == '\t' {
            var spacesToAdd := tabsize - (resultIdx % tabsize);
            if (spacesToAdd == 0) {
                spacesToAdd := tabsize;
            }
            for k := 0 to spacesToAdd - 1 {
                result[resultIdx] := ' ';
                resultIdx := resultIdx + 1;
            }
        } else {
            result[resultIdx] := s[i];
            resultIdx := resultIdx + 1;
        }
    }
    return result[..resultIdx];
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
/* code modified by LLM (iteration 5): no changes required in this section for the current error */
{
    var newResult := new string[|a|];
    for i := 0 to |a| - 1
        invariant 0 <= i <= |a|
        invariant |newResult[..i]| == i
        invariant forall j :: 0 <= j < i ==> NoTabs(newResult[j])
        invariant forall j :: 0 <= j < i ==> (!ContainsTabs(a[j]) ==> newResult[j] == a[j])
        invariant forall j :: 0 <= j < i ==> |newResult[j]| >= |a[j]|
        invariant forall j :: 0 <= j < i ==> (ContainsTabs(a[j]) ==> |newResult[j]| > |a[j]|)
        invariant forall j :: 0 <= j < i ==> NonTabCharsPreserved(a[j], newResult[j])
    {
        newResult[i] := ExpandStringTabs(a[i], tabsize[i]);
    }
    return newResult;
}
// </vc-code>
