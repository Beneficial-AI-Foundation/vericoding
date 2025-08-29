datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma longestHelperPreservesInvariant(strings: seq<string>, index: int, current: string)
    requires 0 <= index < |strings|
    requires strings != []
    requires current in strings
    requires forall i :: 0 <= i < index ==> |current| >= |strings[i]|
    requires exists k :: 0 <= k < index && strings[k] == current
    ensures |strings[index]| > |current| ==> strings[index] in strings
    ensures |strings[index]| > |current| ==> exists k :: 0 <= k <= index && strings[k] == strings[index]
    ensures |strings[index]| <= |current| ==> exists k :: 0 <= k <= index && strings[k] == current
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
function longest(strings: seq<string>): Option<string>
    ensures strings == [] ==> longest(strings) == None
    ensures strings != [] ==> longest(strings) != None
    ensures strings != [] ==> getVal(longest(strings)) in strings
    ensures strings != [] ==> forall s :: s in strings ==> |getVal(longest(strings))| >= |s|
    ensures strings != [] ==> forall i :: 0 <= i < |strings| && |strings[i]| == |getVal(longest(strings))| ==> 
        exists j :: 0 <= j <= i && strings[j] == getVal(longest(strings)) && |strings[j]| == |getVal(longest(strings))|
// </vc-spec>
// <vc-code>
function longest(strings: seq<string>): Option<string>
    ensures strings == [] ==> longest(strings) == None
    ensures strings != [] ==> longest(strings) != None
    ensures strings != [] ==> getVal(longest(strings)) in strings
    ensures strings != [] ==> forall s :: s in strings ==> |getVal(longest(strings))| >= |s|
    ensures strings != [] ==> forall i :: 0 <= i < |strings| && |strings[i]| == |getVal(longest(strings))| ==> 
        exists j :: 0 <= j <= i && strings[j] == getVal(longest(strings)) && |strings[j]| == |getVal(longest(strings))|
{
    if strings == [] then
        None
    else
        longestHelper(strings, 1, strings[0])
}

function longestHelper(strings: seq<string>, index: int, current: string): Option<string>
    requires 0 <= index <= |strings|
    requires strings != []
    requires current in strings
    requires forall i :: 0 <= i < index ==> |current| >= |strings[i]|
    requires exists k :: 0 <= k < index && strings[k] == current
    ensures longestHelper(strings, index, current) != None
    ensures getVal(longestHelper(strings, index, current)) in strings
    ensures forall i :: 0 <= i < |strings| ==> |getVal(longestHelper(strings, index, current))| >= |strings[i]|
    ensures forall i :: 0 <= i < |strings| && |strings[i]| == |getVal(longestHelper(strings, index, current))| ==> 
        exists j :: 0 <= j <= i && strings[j] == getVal(longestHelper(strings, index, current)) && |strings[j]| == |getVal(longestHelper(strings, index, current))|
    decreases |strings| - index
{
    if index == |strings| then
        Some(current)
    else
        if |strings[index]| > |current| then
            longestHelper(strings, index + 1, strings[index])
        else
            longestHelper(strings, index + 1, current)
}
// </vc-code>
