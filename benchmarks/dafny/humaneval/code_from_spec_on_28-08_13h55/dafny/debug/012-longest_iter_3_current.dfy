datatype Option<T> = None | Some(T)
function getVal(mx : Option<string>) : string
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma longestHelperPreservesFirstOccurrence(strings: seq<string>, index: int, current: string)
    requires 0 <= index <= |strings|
    requires strings != []
    requires current in strings
    requires forall i :: 0 <= i < index ==> |current| >= |strings[i]|
    requires (exists j :: 0 <= j < index && strings[j] == current) || (index == 0 && current == strings[0])
    ensures forall i :: 0 <= i < |strings| && |strings[i]| == |getVal(longestHelper(strings, index, current))| ==> exists j :: 0 <= j <= i && strings[j] == getVal(longestHelper(strings, index, current))
    decreases |strings| - index
{
    var result := longestHelper(strings, index, current);
    var resultVal := getVal(result);
    
    if index == |strings| {
        // Base case: current is returned
        assert resultVal == current;
        forall i | 0 <= i < |strings| && |strings[i]| == |resultVal|
            ensures exists j :: 0 <= j <= i && strings[j] == resultVal
        {
            if exists j :: 0 <= j < index && strings[j] == current {
                var j :| 0 <= j < index && strings[j] == current;
                assert j <= i;
                assert strings[j] == resultVal;
            } else {
                assert index == 0 && current == strings[0];
                assert 0 <= i;
                assert strings[0] == resultVal;
            }
        }
    } else if |strings[index]| > |current| {
        // Recursive case: switch to strings[index]
        longestHelperPreservesFirstOccurrence(strings, index + 1, strings[index]);
    } else {
        // Recursive case: keep current
        longestHelperPreservesFirstOccurrence(strings, index + 1, current);
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def longest(strings: List[str]) -> Optional[str]
Out of list of strings, return the longest one. Return the first one in case of multiple strings of the same length. Return None in case the input list is empty.
*/
// </vc-description>

// <vc-code>
function longest(strings: seq<string>) : Option<string>
    ensures strings == [] ==> longest(strings) == None
    ensures strings != [] ==> longest(strings) != None
    ensures strings != [] ==> getVal(longest(strings)) in strings
    ensures strings != [] ==> forall s :: s in strings ==> |getVal(longest(strings))| >= |s|
    ensures strings != [] ==> forall i :: 0 <= i < |strings| && |strings[i]| == |getVal(longest(strings))| ==> exists j :: 0 <= j <= i && strings[j] == getVal(longest(strings))
{
    if strings == [] then
        None
    else
        longestHelper(strings, 0, strings[0])
}

function longestHelper(strings: seq<string>, index: int, current: string) : Option<string>
    requires 0 <= index <= |strings|
    requires strings != []
    requires current in strings
    requires forall i :: 0 <= i < index ==> |current| >= |strings[i]|
    requires (exists j :: 0 <= j < index && strings[j] == current) || (index == 0 && current == strings[0])
    ensures longestHelper(strings, index, current) != None
    ensures getVal(longestHelper(strings, index, current)) in strings
    ensures forall s :: s in strings ==> |getVal(longestHelper(strings, index, current))| >= |s|
    ensures forall i :: 0 <= i < |strings| && |strings[i]| == |getVal(longestHelper(strings, index, current))| ==> exists j :: 0 <= j <= i && strings[j] == getVal(longestHelper(strings, index, current))
    decreases |strings| - index
{
    if index == |strings| then
        longestHelperPreservesFirstOccurrence(strings, index, current);
        Some(current)
    else if |strings[index]| > |current| then
        longestHelper(strings, index + 1, strings[index])
    else
        longestHelper(strings, index + 1, current)
}
// </vc-code>
