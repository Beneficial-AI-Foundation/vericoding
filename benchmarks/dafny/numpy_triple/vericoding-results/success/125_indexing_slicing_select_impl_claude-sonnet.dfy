// <vc-preamble>
/*
 * Dafny specification for numpy.select: Return an array drawn from elements 
 * in choicelist, depending on conditions.
 * 
 * For each element position, returns the element from the first choice array
 * where the corresponding condition is True. If no conditions are True,
 * returns the default value.
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed FirstTrueIndex to properly establish preconditions for assertions */
function FirstTrueIndex(condlist: seq<seq<bool>>, pos: int): int
    requires 0 <= pos
    requires forall i :: 0 <= i < |condlist| ==> |condlist| == 0 || |condlist[i]| == |condlist[0]|
    requires |condlist| == 0 || pos < |condlist[0]|
{
    if |condlist| == 0 then -1
    else if condlist[0][pos] then 0
    else if |condlist| == 1 then -1
    else 
        var subResult := FirstTrueIndex(condlist[1..], pos);
        if subResult == -1 then -1 else subResult + 1
}

function SelectElement(condlist: seq<seq<bool>>, choicelist: seq<seq<real>>, default: real, pos: int): real
    requires |condlist| == |choicelist|
    requires 0 <= pos
    requires forall i :: 0 <= i < |condlist| ==> |condlist| == 0 || |condlist[i]| == |condlist[0]|
    requires forall i :: 0 <= i < |choicelist| ==> |choicelist| == 0 || |choicelist[i]| == |choicelist[0]|
    requires |condlist| == 0 || (|condlist[0]| == |choicelist[0]| && pos < |condlist[0]|)
{
    var firstTrue := FirstTrueIndex(condlist, pos);
    if firstTrue == -1 then default
    else if 0 <= firstTrue < |choicelist| then choicelist[firstTrue][pos]
    else default
}

lemma FirstTrueIndexProperties(condlist: seq<seq<bool>>, pos: int)
    requires 0 <= pos
    requires forall i :: 0 <= i < |condlist| ==> |condlist| == 0 || |condlist[i]| == |condlist[0]|
    requires |condlist| == 0 || pos < |condlist[0]|
    ensures var firstTrue := FirstTrueIndex(condlist, pos);
        if firstTrue == -1 then 
            forall j :: 0 <= j < |condlist| ==> !condlist[j][pos]
        else 
            0 <= firstTrue < |condlist| && 
            condlist[firstTrue][pos] &&
            (forall k :: 0 <= k < firstTrue ==> !condlist[k][pos])
{
    var firstTrue := FirstTrueIndex(condlist, pos);
    if |condlist| == 0 {
        // Base case
    } else if condlist[0][pos] {
        // First element is true
    } else if |condlist| == 1 {
        // Only one element and it's false
    } else {
        // Recursive case
        var subResult := FirstTrueIndex(condlist[1..], pos);
        FirstTrueIndexProperties(condlist[1..], pos);
        if subResult != -1 {
            assert condlist[1..][subResult][pos];
            assert condlist[subResult + 1][pos];
        }
    }
}

lemma SelectElementCorrect(condlist: seq<seq<bool>>, choicelist: seq<seq<real>>, default: real, pos: int)
    requires |condlist| == |choicelist|
    requires 0 <= pos
    requires forall i :: 0 <= i < |condlist| ==> |condlist| == 0 || |condlist[i]| == |condlist[0]|
    requires forall i :: 0 <= i < |choicelist| ==> |choicelist| == 0 || |choicelist[i]| == |choicelist[0]|
    requires |condlist| == 0 || (|condlist[0]| == |choicelist[0]| && pos < |condlist[0]|)
    ensures var element := SelectElement(condlist, choicelist, default, pos);
        ((exists j :: 0 <= j < |condlist| && 
            condlist[j][pos] && 
            element == choicelist[j][pos] &&
            (forall k :: 0 <= k < j ==> !condlist[k][pos])) ||
        ((forall j :: 0 <= j < |condlist| ==> !condlist[j][pos]) && 
            element == default))
{
    FirstTrueIndexProperties(condlist, pos);
    var firstTrue := FirstTrueIndex(condlist, pos);
    var element := SelectElement(condlist, choicelist, default, pos);
    
    if firstTrue == -1 {
        assert forall j :: 0 <= j < |condlist| ==> !condlist[j][pos];
        assert element == default;
    } else {
        assert 0 <= firstTrue < |condlist|;
        assert condlist[firstTrue][pos];
        assert forall k :: 0 <= k < firstTrue ==> !condlist[k][pos];
        assert element == choicelist[firstTrue][pos];
    }
}
// </vc-helpers>

// <vc-spec>
method Select(condlist: seq<seq<bool>>, choicelist: seq<seq<real>>, default: real) 
    returns (result: seq<real>)
    // Preconditions: condlist and choicelist have same length and consistent inner lengths
    requires |condlist| == |choicelist|
    requires forall i :: 0 <= i < |condlist| ==> 
        (|condlist| > 0 ==> |condlist[i]| == |condlist[0]|)
    requires forall i :: 0 <= i < |choicelist| ==> 
        (|choicelist| > 0 ==> |choicelist[i]| == |choicelist[0]|)
    requires |condlist| == 0 || (|condlist[0]| == |choicelist[0]|)
    
    // Postconditions: result has correct length and element-wise selection behavior
    ensures |condlist| == 0 ==> |result| == 0
    ensures |condlist| > 0 ==> |result| == |condlist[0]|
    ensures forall pos :: 0 <= pos < |result| ==>
        // Either some condition matches and we use first matching choice
        ((exists j :: 0 <= j < |condlist| && 
            condlist[j][pos] && 
            result[pos] == choicelist[j][pos] &&
            (forall k :: 0 <= k < j ==> !condlist[k][pos])) ||
        // Or no conditions match and we use default
        ((forall j :: 0 <= j < |condlist| ==> !condlist[j][pos]) && 
            result[pos] == default))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added FirstTrueIndexProperties lemma call to establish proper invariants */
    if |condlist| == 0 {
        result := [];
        return;
    }
    
    var length := |condlist[0]|;
    result := [];
    
    var pos := 0;
    while pos < length
        invariant 0 <= pos <= length
        invariant |result| == pos
        invariant forall i :: 0 <= i < pos ==> 
            result[i] == SelectElement(condlist, choicelist, default, i)
        invariant forall i :: 0 <= i < pos ==> 
            ((exists j :: 0 <= j < |condlist| && 
                condlist[j][i] && 
                result[i] == choicelist[j][i] &&
                (forall k :: 0 <= k < j ==> !condlist[k][i])) ||
            ((forall j :: 0 <= j < |condlist| ==> !condlist[j][i]) && 
                result[i] == default))
    {
        FirstTrueIndexProperties(condlist, pos);
        var element := SelectElement(condlist, choicelist, default, pos);
        SelectElementCorrect(condlist, choicelist, default, pos);
        result := result + [element];
        pos := pos + 1;
    }
}
// </vc-code>
