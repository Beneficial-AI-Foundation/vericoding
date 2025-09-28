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
  /* code modified by LLM (iteration 4): fixed parentheses around exists expression to resolve indentation warning */
  if |condlist| == 0 {
    result := [];
  } else {
    var n := |condlist[0]|;
    result := [];
    var pos := 0;
    while pos < n
      invariant 0 <= pos <= n
      invariant |result| == pos
      invariant forall p :: 0 <= p < pos ==>
        ((exists j :: 0 <= j < |condlist| && 
            condlist[j][p] && 
            result[p] == choicelist[j][p] &&
            (forall k :: 0 <= k < j ==> !condlist[k][p])) ||
        ((forall j :: 0 <= j < |condlist| ==> !condlist[j][p]) && 
            result[p] == default))
    {
      var found := false;
      var j := 0;
      var value := default;
      while j < |condlist|
        invariant 0 <= j <= |condlist|
        invariant !found ==> (forall k :: 0 <= k < j ==> !condlist[k][pos])
        invariant found ==> (exists k :: (0 <= k < j && 
            condlist[k][pos] && 
            value == choicelist[k][pos] &&
            (forall m :: 0 <= m < k ==> !condlist[m][pos])))
        invariant !found ==> value == default
      {
        if !found && condlist[j][pos] {
          value := choicelist[j][pos];
          found := true;
        }
        j := j + 1;
      }
      result := result + [value];
      pos := pos + 1;
    }
  }
}
// </vc-code>
