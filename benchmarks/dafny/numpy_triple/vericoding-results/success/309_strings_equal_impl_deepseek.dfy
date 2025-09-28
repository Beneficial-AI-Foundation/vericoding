// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function StringEq(s1: string, s2: string): bool {
  s1 == s2
}

lemma StringEqLemma(s1: string, s2: string)
  ensures (s1 == s2) <==> StringEq(s1, s2)
{
}

// </vc-helpers>

// <vc-spec>
method Equal(x1: seq<string>, x2: seq<string>) returns (result: seq<bool>)
  requires |x1| == |x2|
  ensures |result| == |x1|
  ensures |result| == |x2|
  // Core property: result[i] = (x1[i] == x2[i]) for all valid indices
  ensures forall i :: 0 <= i < |result| ==> result[i] == (x1[i] == x2[i])
  // Equivalence: result[i] is true if and only if strings are equal
  ensures forall i :: 0 <= i < |result| ==> (result[i] <==> x1[i] == x2[i])
  // Reflexivity: if input sequences are identical, all result elements are true
  ensures x1 == x2 ==> (forall i :: 0 <= i < |result| ==> result[i] == true)
// </vc-spec>
// <vc-code>
{
  result := [];
  var index := 0;
  while index < |x1|
    invariant index <= |x1|
    invariant |result| == index
    invariant forall i :: 0 <= i < index ==> result[i] == (x1[i] == x2[i])
  {
    result := result + [StringEq(x1[index], x2[index])];
    index := index + 1;
  }
}
// </vc-code>
