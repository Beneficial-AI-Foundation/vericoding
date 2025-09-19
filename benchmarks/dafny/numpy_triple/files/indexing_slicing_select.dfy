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
  assume {:axiom} false;
}
// </vc-code>
