// <vc-preamble>
/*
 * Dafny specification for numpy.putmask functionality.
 * Changes elements of an array based on conditional and input values,
 * with cyclic repetition of values when the values array is smaller.
 */
// </vc-preamble>

// <vc-helpers>
function GetValue(values: seq<real>, index: int): real
  requires |values| > 0
  requires index >= 0
{
  values[index % |values|]
}

lemma GetValueCyclic(values: seq<real>, i: int, j: int)
  requires |values| > 0
  requires i >= 0 && j >= 0
  ensures i % |values| == j % |values| ==> GetValue(values, i) == GetValue(values, j)
{
}

/* helper modified by LLM (iteration 2): Added lemma to prove index bounds */
lemma IndexBoundsLemma(a: seq<real>, mask: seq<bool>, values: seq<real>, k: int)
  requires |a| == |mask|
  requires |values| > 0
  requires 0 <= k < |a|
  ensures 0 <= k < |mask|
  ensures 0 <= k < |a|
{
}
// </vc-helpers>

// <vc-spec>
method putmask(a: seq<real>, mask: seq<bool>, values: seq<real>) returns (result: seq<real>)
    // Preconditions: arrays must have same length, values must be non-empty
    requires |a| == |mask|
    requires |values| > 0
    
    // Postconditions: specify the exact behavior of putmask
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> 
        (mask[i] ==> result[i] == values[i % |values|])
    ensures forall i :: 0 <= i < |result| ==> 
        (!mask[i] ==> result[i] == a[i])
    ensures forall i :: 0 <= i < |result| ==> 
        (mask[i] ==> exists j :: 0 <= j < |values| && result[i] == values[j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed index bounds verification */
  result := [];
  var index := 0;
  while index < |a|
    invariant |result| == index
    invariant 0 <= index <= |a|
    invariant forall k :: 0 <= k < index ==> 
        (mask[k] ==> result[k] == GetValue(values, k))
    invariant forall k :: 0 <= k < index ==> 
        (!mask[k] ==> result[k] == a[k])
  {
    if mask[index] {
      result := result + [GetValue(values, index)];
    } else {
      result := result + [a[index]];
    }
    index := index + 1;
  }
}
// </vc-code>
