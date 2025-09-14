// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed Tail to handle empty seq and added lemma proof */
function Tail(a: seq<int>): seq<int> { if |a| == 0 then [] else a[1..] }

lemma TailProperties(a: seq<int>)
  requires |a| > 0
  ensures |Tail(a)| == |a| - 1
  ensures forall i :: 0 <= i < |Tail(a)| ==> Tail(a)[i] == a[i + 1]
{
  // For non-empty a, by definition Tail(a) == a[1..]
  assert Tail(a) == a[1..];
  // Length of the slice a[1..] is |a| - 1
  assert |Tail(a)| == |a| - 1;
  // Element-wise equality follows from the slice semantics
  assert forall i :: 0 <= i < |Tail(a)| ==> Tail(a)[i] == a[i + 1];
}

// </vc-helpers>

// <vc-spec>
method RemoveFront(a: seq<int>) returns (result: seq<int>)
    requires |a| > 0
    ensures |a| > 0
    ensures |result| == |a| - 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): return tail of the sequence using Tail helper */
  result := Tail(a);
}

// </vc-code>
