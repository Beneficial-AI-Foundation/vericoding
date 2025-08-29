datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
function max(a: int, b: int): int
{
    if a >= b then a else b
}

lemma MaxProperty(a: int, b: int)
    ensures max(a, b) >= a && max(a, b) >= b
    ensures max(a, b) == a || max(a, b) == b
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def longest(strings: List[str]) -> Optional[str]
Out of list of strings, return the longest one. Return the first one in case of multiple strings of the same length. Return None in case the input list is empty.
*/
// </vc-description>

// <vc-spec>
method longest(strings: seq<string>) returns (result: Option<string>)
    ensures |strings| == 0 ==> result == None
    ensures |strings| > 0 ==> result != None
    ensures |strings| > 0 ==> exists i :: 0 <= i < |strings| && result == Some(strings[i])
    ensures |strings| > 0 ==> forall j :: 0 <= j < |strings| ==> |getVal(result)| >= |strings[j]|
    ensures |strings| > 0 ==> forall i :: 0 <= i < |strings| && |strings[i]| == |getVal(result)| ==> 
        exists k :: 0 <= k < |strings| && strings[k] == getVal(result) && k <= i
// </vc-spec>
// <vc-code>
{
    if |strings| == 0 {
        return None;
    }
    
    var maxLen := |strings[0]|;
    var maxIndex := 0;
    var i := 1;
    
    while i < |strings|
        invariant 0 <= i <= |strings|
        invariant 0 <= maxIndex < |strings|
        invariant maxLen == |strings[maxIndex]|
        invariant forall j :: 0 <= j < i ==> |strings[j]| <= maxLen
        invariant forall j :: 0 <= j < i && |strings[j]| == maxLen ==> j >= maxIndex
    {
        if |strings[i]| > maxLen {
            maxLen := |strings[i]|;
            maxIndex := i;
        }
        i := i + 1;
    }
    
    return Some(strings[maxIndex]);
}
// </vc-code>
