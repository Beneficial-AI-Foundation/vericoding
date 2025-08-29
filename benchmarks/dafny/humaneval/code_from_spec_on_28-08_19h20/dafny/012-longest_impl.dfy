datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
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
    ensures |strings| > 0 ==> getVal(result) in strings
    ensures |strings| > 0 ==> forall s :: s in strings ==> |getVal(result)| >= |s|
    ensures |strings| > 0 ==> forall i :: 0 <= i < |strings| && strings[i] == getVal(result) ==> 
        exists j :: 0 <= j <= i && strings[j] == getVal(result) && |strings[j]| == |getVal(result)|
// </vc-spec>
// <vc-code>
method longest(strings: seq<string>) returns (result: Option<string>)
    ensures |strings| == 0 ==> result == None
    ensures |strings| > 0 ==> result != None
    ensures |strings| > 0 ==> getVal(result) in strings
    ensures |strings| > 0 ==> forall s :: s in strings ==> |getVal(result)| >= |s|
    ensures |strings| > 0 ==> forall i :: 0 <= i < |strings| && strings[i] == getVal(result) ==> 
        exists j :: 0 <= j <= i && strings[j] == getVal(result) && |strings[j]| == |getVal(result)|
{
    if |strings| == 0 {
        result := None;
    } else {
        var maxLen := |strings[0]|;
        var maxIndex := 0;
        var i := 1;
        
        while i < |strings|
            invariant 1 <= i <= |strings|
            invariant 0 <= maxIndex < |strings|
            invariant maxLen == |strings[maxIndex]|
            invariant forall k :: 0 <= k < i ==> |strings[k]| <= maxLen
            invariant forall k :: 0 <= k < i && |strings[k]| == maxLen ==> maxIndex <= k
        {
            if |strings[i]| > maxLen {
                maxLen := |strings[i]|;
                maxIndex := i;
            }
            i := i + 1;
        }
        
        result := Some(strings[maxIndex]);
    }
}
// </vc-code>
